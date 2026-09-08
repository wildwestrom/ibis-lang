import Ibis.Eval

namespace Ibis

structure CheckCtx where
  env : List Value := []
  types : List Value := []
  globals : Globals := []
  signatures : List (String × Core) := []
  deriving Inhabited

abbrev CheckM := ReaderT CheckCtx (Except String)
private def runEval (e : EvalM α) : CheckM α := do e (← read).globals
private def value (t : Core) : CheckM Value := do runEval (eval (← read).env t)
private def withBinding (v ty : Value) (action : CheckM α) : CheckM α :=
  withReader (fun c => { c with env := v :: c.env, types := ty :: c.types }) action
private def fresh : CheckM Value := return .neutral (.var (← read).env.length)
private def level : Value → CheckM Nat
  | .universe n => pure n
  | _ => throw "expected a universe"

private def builtinType (n : String) : Option Core :=
  let arrow a b := Core.pi none a b
  let int := Core.const "Int"
  let bool := Core.const "Bool"
  if ["Nat", "Int", "Float", "Bool", "String", "Unit", "Site"].contains n then some (.universe 1)
  else if ["+", "-", "*", "/"].contains n then some (arrow int (arrow int int))
  else if ["==", "!=", "<", ">", "<=", ">="].contains n then some (arrow int (arrow int bool))
  else if ["and", "or", "==>"].contains n then some (arrow bool (arrow bool bool))
  else if n == "negate" then some (arrow int int)
  else if n == "not" then some (arrow bool bool)
  else none

mutual
  partial def check (t : Core) (expected : Value) : CheckM Unit := do
    match t, expected with
    | .lam _ b, .pi _ dom env cod =>
      let x ← fresh
      let ty ← runEval (eval (x :: env) cod)
      withBinding x dom (check b ty)
    | .pair a b, .sigma _ dom env cod =>
      check a dom
      check b (← runEval (eval ((← value a) :: env) cod))
    | .lit (.int n), .const "Nat" [] =>
      if n < 0 then throw "negative literal cannot have type Nat"
    | .matchE e bs, _ => checkMatch e bs expected
    | .letE e b, _ =>
      let ty ← infer e
      withBinding (← value e) ty (check b expected)
    | _, _ =>
      let got ← infer t
      let depth := (← read).env.length
      unless ← runEval (convert depth got expected) do
        let a ← runEval (quote depth expected)
        let b ← runEval (quote depth got)
        throw s!"type mismatch: expected {a.pretty}, inferred {b.pretty}"

  partial def infer (t : Core) : CheckM Value := do
    match t with
    | .universe n => pure (.universe (n + 1))
    | .const n =>
      match (← read).signatures.lookup n |>.orElse (fun _ => builtinType n) with
      | some ty => value ty
      | none => throw s!"unknown constant '{n}'"
    | .var n => match (← read).types[n]? with
      | some ty => pure ty
      | none => throw s!"unbound type variable index {n}"
    | .lit l => pure (.const (match l with
        | .int _ => "Int" | .float _ => "Float" | .bool _ => "Bool" | .string _ => "String") [])
    | .unit => pure (.const "Unit" [])
    | .pi _ a b | .sigma _ a b =>
      let u ← level (← infer a)
      let dom ← value a
      let v ← withBinding (← fresh) dom (do level (← infer b))
      pure (.universe (max u v))
    | .app f x =>
      match ← infer f with
      | .pi _ dom env cod =>
        check x dom
        runEval (eval ((← value x) :: env) cod)
      | _ => throw "application requires a dependent function type"
    | .fst p => match ← infer p with
      | .sigma _ dom _ _ => pure dom
      | _ => throw "fst requires a dependent pair type"
    | .snd p => match ← infer p with
      | .sigma _ _ env cod => runEval (eval ((← runEval (evalFst (← value p))) :: env) cod)
      | _ => throw "snd requires a dependent pair type"
    | .ann e ty =>
      let _ ← level (← infer ty)
      let ty ← value ty
      check e ty
      pure ty
    | .letE e b =>
      let ty ← infer e
      withBinding (← value e) ty (infer b)
    | .site _ => pure (.const "Site" [])
    | .cover u v =>
      check u (.const "Site" [])
      check v (.const "Site" [])
      pure (.universe 0)
    | .sect a u =>
      let l ← level (← infer a)
      check u (.const "Site" [])
      pure (.universe l)
    | .res a u v p s =>
      checkTransport a u v p
      check s (← value (.sect a v))
      value (.sect a u)
    | .ext a u v p s =>
      checkTransport a u v p
      check s (← value (.sect a u))
      value (.sect a v)
    | .lam _ _ => throw "cannot infer a lambda; provide a Pi type annotation"
    | .pair _ _ => throw "cannot infer a pair; provide a Sigma type annotation"
    | .matchE _ _ => throw "cannot infer a match; provide a result type annotation"
    | .mvar n => throw s!"unsolved metavariable ?{n}"

  private partial def checkTransport (a u v p : Core) : CheckM Unit := do
    let _ ← level (← infer a)
    check u (.const "Site" [])
    check v (.const "Site" [])
    check p (← value (.cover u v))

  private partial def checkMatch (e : Core) (bs : List (Pat × Core)) (expected : Value) : CheckM Unit := do
    let ty ← infer e
    let mut catchAll := false
    let mut bools : List Bool := []
    for (p, b) in bs do
      match p with
      | .wildcard => check b expected; catchAll := true
      | .capture _ => withBinding (← value e) ty (check b expected); catchAll := true
      | .lit l =>
        check (.lit l) ty
        check b expected
        if let .bool x := l then bools := x :: bools
      | _ => throw "checking constructor and tuple patterns requires dependent elimination (not implemented)"
    unless catchAll || (bools.contains true && bools.contains false) do
      throw "match is not known to be exhaustive"
end

def inferType (t : Core) (ctx : CheckCtx := {}) : Except String Core := do
  let ty ← infer t ctx
  quote ctx.env.length ty ctx.globals

/-- Checks definitions sequentially; declaring inductives needs a positivity/recursor checker. -/
def checkProgram (ds : List CoreDecl) : Except String CheckCtx := do
  let mut ctx : CheckCtx := {}
  for d in ds do
    match d with
    | .defn "<anonymous>" _ b => let _ ← infer b ctx
    | .defn n ty b =>
      if ctx.signatures.contains (n, ty) || (ctx.signatures.lookup n).isSome then
        throw s!"duplicate definition '{n}'"
      let _ ← (do level (← infer ty)) ctx
      let v ← eval [] ty ctx.globals
      check b v ctx
      ctx := { ctx with signatures := (n, ty) :: ctx.signatures, globals := (n, b) :: ctx.globals }
    | .inductiveE n _ _ => throw s!"checking inductive '{n}' requires positivity and recursor generation (not implemented)"
  pure ctx

end Ibis
