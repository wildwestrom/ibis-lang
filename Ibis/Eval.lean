import Ibis.Syntax

namespace Ibis

abbrev Globals := List (String × Core)

mutual
  inductive Value where
    | universe : Nat → Value
    | const : String → List Value → Value
    | lit : Literal → Value
    | unit
    | pi : Option String → Value → List Value → Core → Value
    | lam : Option String → List Value → Core → Value
    | sigma : Option String → Value → List Value → Core → Value
    | pair : Value → Value → Value
    | site : Nat → Value
    | cover : Value → Value → Value
    | sect : Value → Value → Value
    | neutral : Neutral → Value
  inductive Neutral where
    | var : Nat → Neutral
    | mvar : Nat → Neutral
    | app : Neutral → Value → Neutral
    | fst : Neutral → Neutral
    | snd : Neutral → Neutral
    | matchE : Neutral → List Value → List (Pat × Core) → Neutral
    | res : Value → Value → Value → Value → Neutral → Neutral
    | ext : Value → Value → Value → Value → Neutral → Neutral
end

instance : Inhabited Value := ⟨.unit⟩
abbrev EvalM := ReaderT Globals (Except String)

private def primitive (name : String) (args : List Value) : Except String Value := do
  match name, args with
  | "negate", [.lit (.int n)] => pure (.lit (.int (-n)))
  | "not", [.lit (.bool b)] => pure (.lit (.bool (!b)))
  | op, [.lit (.int a), .lit (.int b)] =>
    match op with
    | "+" => pure (.lit (.int (a + b)))
    | "-" => pure (.lit (.int (a - b)))
    | "*" => pure (.lit (.int (a * b)))
    | "/" => if b == 0 then throw "division by zero" else pure (.lit (.int (a / b)))
    | "==" => pure (.lit (.bool (a == b)))
    | "!=" => pure (.lit (.bool (a != b)))
    | "<" => pure (.lit (.bool (a < b)))
    | ">" => pure (.lit (.bool (a > b)))
    | "<=" => pure (.lit (.bool (a ≤ b)))
    | ">=" => pure (.lit (.bool (a ≥ b)))
    | _ => pure (.const name args)
  | "and", [.lit (.bool a), .lit (.bool b)] => pure (.lit (.bool (a && b)))
  | "or", [.lit (.bool a), .lit (.bool b)] => pure (.lit (.bool (a || b)))
  | "==>", [.lit (.bool a), .lit (.bool b)] => pure (.lit (.bool (!a || b)))
  | _, _ => pure (.const name args)

private def flattenPair : Value → List Value
  | .pair a b => a :: flattenPair b
  | v => [v]

mutual
  partial def matchPattern (p : Pat) (v : Value) : Option (List Value) :=
    match p, v with
    | .wildcard, _ => some []
    | .capture _, v => some [v]
    | .lit a, .lit b => if a == b then some [] else none
    | .tuple ps, v => matchPatterns ps (flattenPair v)
    | .ctor n ps, .const m vs => if n == m then matchPatterns ps vs else none
    | .partition n p, .const "cons" [hd, tl] => do
      let vs ← matchPattern p tl
      pure (vs ++ if n == "_" then [] else [hd])
    | _, _ => none
  private partial def matchPatterns (ps : List Pat) (vs : List Value) : Option (List Value) :=
    match ps, vs with
    | [], [] => some []
    | p :: ps, v :: vs => do
      let first ← matchPattern p v
      let rest ← matchPatterns ps vs
      pure (rest ++ first)
    | _, _ => none
end

mutual
  partial def eval (env : List Value) (t : Core) : EvalM Value := do
    match t with
    | .universe n => pure (.universe n)
    | .const n =>
      match (← read).lookup n with
      | some body => eval [] body
      | none => pure (.const n [])
    | .mvar n => pure (.neutral (.mvar n))
    | .var n => match env[n]? with
      | some v => pure v
      | none => throw s!"unbound variable index {n}"
    | .lit l => pure (.lit l)
    | .unit => pure .unit
    | .pi n a b => return .pi n (← eval env a) env b
    | .lam n b => pure (.lam n env b)
    | .app f x => applyVal (← eval env f) (← eval env x)
    | .sigma n a b => return .sigma n (← eval env a) env b
    | .pair a b => return .pair (← eval env a) (← eval env b)
    | .fst p => evalFst (← eval env p)
    | .snd p => evalSnd (← eval env p)
    | .letE e b => eval ((← eval env e) :: env) b
    | .ann e _ => eval env e
    | .matchE e bs => evalMatch env (← eval env e) bs
    | .site n => pure (.site n)
    | .cover u v => return .cover (← eval env u) (← eval env v)
    | .sect a u => return .sect (← eval env a) (← eval env u)
    | .res a u v p s =>
      let a ← eval env a; let u ← eval env u; let v ← eval env v; let p ← eval env p
      match ← eval env s with
      | .neutral n => pure (.neutral (.res a u v p n))
      | s => pure s
    | .ext a u v p s =>
      let a ← eval env a; let u ← eval env u; let v ← eval env v; let p ← eval env p
      match ← eval env s with
      | .neutral n => pure (.neutral (.ext a u v p n))
      | s => pure s

  partial def applyVal (f x : Value) : EvalM Value := do
    match f with
    | .lam _ env body => eval (x :: env) body
    | .neutral n => pure (.neutral (.app n x))
    | .const n args => primitive n (args ++ [x])
    | _ => throw "cannot apply a non-function value"

  partial def evalFst (p : Value) : EvalM Value :=
    match p with
    | .pair a _ => pure a
    | .neutral n => pure (.neutral (.fst n))
    | _ => throw "cannot take fst of a non-pair"

  partial def evalSnd (p : Value) : EvalM Value :=
    match p with
    | .pair _ b => pure b
    | .neutral n => pure (.neutral (.snd n))
    | _ => throw "cannot take snd of a non-pair"

  partial def evalMatch (env : List Value) (v : Value) (bs : List (Pat × Core)) : EvalM Value :=
    match v with
    | .neutral n => pure (.neutral (.matchE n env bs))
    | _ => match bs with
      | [] => throw "non-exhaustive pattern match"
      | (p, b) :: rest => match matchPattern p v with
        | some bindings => eval (bindings ++ env) b
        | none => evalMatch env v rest

  partial def quote (depth : Nat) (v : Value) : EvalM Core := do
    match v with
    | .universe n => pure (.universe n)
    | .const n args => return (← args.mapM (quote depth)).foldl Core.app (.const n)
    | .lit l => pure (.lit l)
    | .unit => pure .unit
    | .pi _ a env b => return .pi none (← quote depth a) (← quote (depth + 1) (← eval (.neutral (.var depth) :: env) b))
    | .lam _ env b => return .lam none (← quote (depth + 1) (← eval (.neutral (.var depth) :: env) b))
    | .sigma _ a env b => return .sigma none (← quote depth a) (← quote (depth + 1) (← eval (.neutral (.var depth) :: env) b))
    | .pair a b => return .pair (← quote depth a) (← quote depth b)
    | .site n => pure (.site n)
    | .cover u v => return .cover (← quote depth u) (← quote depth v)
    | .sect a u => return .sect (← quote depth a) (← quote depth u)
    | .neutral n => quoteNeutral depth n

  partial def quoteNeutral (depth : Nat) (n : Neutral) : EvalM Core := do
    match n with
    | .var level =>
      if level ≥ depth then throw s!"escaping variable level {level} at depth {depth}"
      pure (.var (depth - level - 1))
    | .mvar n => pure (.mvar n)
    | .app f x => return .app (← quoteNeutral depth f) (← quote depth x)
    | .fst p => return .fst (← quoteNeutral depth p)
    | .snd p => return .snd (← quoteNeutral depth p)
    | .matchE n env bs =>
      let bs ← bs.mapM fun (p, b) => do
        let count := p.vars.length
        let fresh := (List.range count).reverse.map fun i => Value.neutral (.var (depth + i))
        return (p, ← quote (depth + count) (← eval (fresh ++ env) b))
      return .matchE (← quoteNeutral depth n) bs
    | .res a u v p n => return .res (← quote depth a) (← quote depth u) (← quote depth v) (← quote depth p) (← quoteNeutral depth n)
    | .ext a u v p n => return .ext (← quote depth a) (← quote depth u) (← quote depth v) (← quote depth p) (← quoteNeutral depth n)
end

def normalize (t : Core) (globals : Globals := []) : Except String Core :=
  (do quote 0 (← eval [] t)) globals

def convert (depth : Nat) (a b : Value) : EvalM Bool := do
  return (← quote depth a) == (← quote depth b)

end Ibis
