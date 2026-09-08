import Ibis.Core

namespace Ibis

structure ElabCtx where
  scope : List String := []
  deriving Inhabited

structure ElabState where
  universes : List (String × Nat) := []
  nextLevel : Nat := 1
  globals : List String := []
  sites : List String := []
  deriving Repr, Inhabited

abbrev ElabM := ReaderT ElabCtx (StateT ElabState (Except String))

private def withNames (ns : List String) (action : ElabM α) : ElabM α :=
  withReader (fun ctx => { ctx with scope := ns.reverse ++ ctx.scope }) action

private def resolve (n : String) (constant : Bool := false) : ElabM Core := do
  let scope := (← read).scope
  if let some i := scope.idxOf? n then return .var i
  if constant || (← get).globals.contains n then return .const n
  throw s!"unbound variable '{n}'"

mutual
  partial def elabTerm (t : Term) : ElabM Core := do
    match t with
    | .universe (.level n) => pure (.universe n)
    | .universe (.named n) =>
      let st ← get
      if let some level := st.universes.lookup n then return .universe level
      set { st with universes := (n, st.nextLevel) :: st.universes, nextLevel := st.nextLevel + 1 }
      pure (.universe st.nextLevel)
    | .const n => resolve n true
    | .var n => resolve n
    | .mvar n => pure (.mvar n)
    | .lit l => pure (.lit l)
    | .unit => pure .unit
    | .pi n a b => return .pi (some n) (← elabTerm a) (← withNames [n] (elabTerm b))
    | .lam n b => return .lam (some n) (← withNames [n] (elabTerm b))
    | .app f x => return .app (← elabTerm f) (← elabTerm x)
    | .sigma n a b => return .sigma (some n) (← elabTerm a) (← withNames [n] (elabTerm b))
    | .pair a b => return .pair (← elabTerm a) (← elabTerm b)
    | .fst p => return .fst (← elabTerm p)
    | .snd p => return .snd (← elabTerm p)
    | .letE n ty e b =>
      let e ← elabTerm e
      let e ← match ty with
        | some ty => return Core.ann e (← elabTerm ty)
        | none => pure e
      return .letE e (← withNames [n] (elabTerm b))
    | .ann e t => return .ann (← elabTerm e) (← elabTerm t)
    | .unop op e => return .app (.const (if op == "-" then "negate" else op)) (← elabTerm e)
    | .binop op a b => return .app (.app (.const op) (← elabTerm a)) (← elabTerm b)
    | .list es =>
      let es ← es.mapM elabTerm
      pure (es.foldr (fun e acc => .app (.app (.const "cons") e) acc) (.const "nil"))
    | .ifE c t e => return .matchE (← elabTerm c) [(.lit (.bool true), ← elabTerm t), (.lit (.bool false), ← elabTerm e)]
    | .forE n xs b => return .app (.app (.const "mapM") (.lam (some n) (← withNames [n] (elabTerm b)))) (← elabTerm xs)
    | .matchE e bs => return .matchE (← elabTerm e) (← bs.mapM fun (p, b) => do
          unless p.vars.eraseDups.length == p.vars.length do throw "duplicate pattern variable"
          return (p, ← withNames p.vars (elabTerm b)))
    | .doE es => elabDo es
    | .bind _ _ => throw "bind is only valid before the final expression of a do block"
    | .site n =>
      if let some i := (← get).sites.idxOf? n then return .site i
      if let some i := (← read).scope.idxOf? n then return .site i
      throw s!"unknown site '{n}'"
    | .cover u v => return .cover (← elabTerm u) (← elabTerm v)
    | .sect a u => return .sect (← elabTerm a) (← elabTerm u)
    | .res _ _ => throw "restriction proof synthesis is not implemented"
    | .ext _ _ _ => throw "extension proof synthesis is not implemented"

  private partial def elabDo : List Term → ElabM Core
    | [] => throw "empty do block"
    | [t] => elabTerm t
    | .bind n e :: rest => do
      let e ← elabTerm e
      let b ← withNames [n] (elabDo rest)
      return .app (.app (.const ">>=") e) (.lam (some n) b)
    | _ => throw "non-final do statements must be bindings"
end

private def piParams (ps : List Param) (body : Term) : Term :=
  ps.foldr (fun (n, ty) b => .pi n ty b) body
private def lamParams (ps : List Param) (body : Term) : Term :=
  ps.foldr (fun (n, _) b => .lam n b) body
private def register (names : List String) : ElabM Unit := do
  for n in names do
    if (← get).globals.contains n then throw s!"duplicate declaration '{n}'"
    modify fun s => { s with globals := n :: s.globals }

private def elabStruct (name : String) (params fields : List Param) : ElabM (List CoreDecl) := do
  let ctor := name ++ "_mk"
  register (name :: ctor :: fields.map (fun f => name ++ "_" ++ f.1))
  let target := params.foldl (fun t p => Term.app t (.var p.1)) (.const name)
  let ty ← elabTerm (piParams params (.universe (.level 1)))
  let ctorTy ← elabTerm (piParams (params ++ fields) target)
  let mut decls := [CoreDecl.inductiveE name ty [(ctor, ctorTy)]]
  let mut previous : List (String × Core) := []
  for (field, idx) in fields.zipIdx do
    let openTy ← withNames (params.map Prod.fst ++ (fields.take idx).map Prod.fst) (elabTerm field.2)
    -- Substitute earlier fields with projections of self, and retain the parameter telescope.
    let projTy : Core := Id.run <| Core.rewriteM (fun depth t => pure <| match t with
      | .var i => if i < depth then t else
          let j := i - depth
          if j < idx then Core.shift depth ((previous.reverse[j]!).2)
          else .var (depth + j - idx + 1)
      | _ => t) 0 openTy
    let selfTy ← withNames (params.map Prod.fst) (elabTerm target)
    let mut fullTy := Core.pi (some "self") selfTy projTy
    -- Parameter types may depend on earlier parameters.
    let paramType ← elabTerm (piParams params (.universe (.level 1)))
    let rec wrap (t : Core) (b : Core) : Core := match t with
      | .pi n a rest => .pi n a (wrap rest b)
      | _ => b
    fullTy := wrap paramType fullTy
    let pat := Pat.ctor ctor (params.map (fun _ => .wildcard) ++ fields.map (fun f => .capture f.1))
    let body := Core.lam (some "self") (.matchE (.var 0) [(pat, .var (fields.length - idx - 1))])
    let body := params.foldr (fun p b => Core.lam (some p.1) b) body
    let projName := name ++ "_" ++ field.1
    decls := decls ++ [.defn projName fullTy body]
    let args := (List.range params.length).map (fun i => Core.var (params.length - i))
    previous := previous ++ [(field.1, .app (args.foldl Core.app (.const projName)) (.var 0))]
  pure decls

def elabDecl : Decl → ElabM (List CoreDecl)
  | .term t => do let t ← elabTerm t; pure [.defn "<anonymous>" t t]
  | .struct n ps fs => elabStruct n ps fs
  | .inductiveE n ps arity cs => do
    register (n :: cs.map Prod.fst)
    let ty ← elabTerm (piParams ps arity)
    let cs ← cs.mapM fun (c, t) => return (c, ← elabTerm (piParams ps t))
    pure [.inductiveE n ty cs]
  | .function n ps ty (.simple b) => do
    -- Non-recursive definitions: recursive declarations need a termination checker.
    let ty ← elabTerm (piParams ps ty)
    let b ← elabTerm (lamParams ps b)
    register [n]
    pure [.defn n ty b]
  | .function _ _ _ (.tactics _) => throw "tactic execution is not implemented"
  | .site n rules => do
    let names := n :: rules.flatMap (fun r => r.parent :: r.children)
    modify fun s => { s with sites := (s.sites ++ names).eraseDups }
    pure []
  | .importE _ _ | .importExposing _ _ => throw "module loading is not implemented"

def elaborate (t : Term) : Except String Core := do
  let (t, _) ← elabTerm t {} {}
  pure t

def elaborateProgram (ds : List Decl) : Except String (List CoreDecl) := do
  let (ds, _) ← (ds.mapM elabDecl) {} {}
  pure ds.flatten

end Ibis
