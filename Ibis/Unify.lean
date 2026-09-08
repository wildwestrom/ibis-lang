import Ibis.Core
import Ibis.Eval

namespace Ibis.Unify

structure Equation where
  type : Core
  lhs : Core
  rhs : Core
  deriving Repr, BEq, Inhabited

inductive ProblemState where
  | active | blocked | solved | failed : String → ProblemState
  deriving Repr, BEq, Inhabited

structure Problem where
  id : Nat
  state : ProblemState
  equation : Equation
  deriving Repr, BEq, Inhabited

inductive Entry where
  | bvar : String → Core → Entry
  | bdef : String → Core → Core → Entry
  | metavariable : Nat → Core → Option Core → Entry
  | problem : Problem → Entry
  deriving Repr, BEq, Inhabited

structure Zip where
  left : List Entry := []
  focus : Option Entry := none
  right : List Entry := []
  deriving Repr, BEq, Inhabited

abbrev Subst := List (Nat × Core)

structure SolverState where
  context : Zip := {}
  subst : Subst := []
  worklist : List Problem := []
  nextMetaId : Nat := 0
  nextProblemId : Nat := 0
  deriving Repr, Inhabited

def Zip.pushL (e : Entry) (z : Zip) : Zip := { z with left := e :: z.left }
def Zip.pushR (e : Entry) (z : Zip) : Zip := { z with right := e :: z.right }
def Zip.popL (z : Zip) : Option Entry × Zip := (z.left.head?, { z with left := z.left.drop 1 })
def Zip.popR (z : Zip) : Option Entry × Zip := (z.right.head?, { z with right := z.right.drop 1 })

/-- Substitutions contain closed lambda terms. Cycle detection also covers caller-provided maps. -/
partial def substitute (s : Subst) (t : Core) (visited : List Nat := []) : Except String Core :=
  Core.rewriteM (fun depth t => do
    match t with
    | .mvar n => match s.lookup n with
      | none => pure t
      | some replacement =>
        if visited.contains n then throw s!"cyclic metavariable substitution ?{n}"
        return Core.shift depth (← substitute s replacement (n :: visited))
    | _ => pure t) 0 t

def buildSpineMap (args : List Core) : Option (List (Nat × Nat)) := do
  let vars ← args.mapM fun t => match t with | .var n => some n | _ => none
  if vars.eraseDups.length != vars.length then none else
    some (vars.zipIdx.map fun (n, i) => (n, vars.length - i - 1))

def invert (target : Nat) (args : List Core) (rhs : Core) : Except String Core := do
  if rhs.freeMetas.contains target then throw "occurs check failed"
  let some mapping := buildSpineMap args | throw "spine is not a linear variable pattern"
  let body ← Core.rewriteM (fun depth t => do
    match t with
    | .var n =>
      if n < depth then return t
      let some i := mapping.lookup (n - depth) | throw "variable escapes metavariable scope"
      pure (.var (i + depth))
    | _ => pure t) 0 rhs
  pure (args.foldr (fun _ b => .lam none b) body)

private def normalOpen (depth : Nat) (t : Core) : Except String Core := do
  let env := (List.range depth).reverse.map fun i => Value.neutral (.var i)
  quote depth (← eval env t []) []

private def assign (m : Nat) (args : List Core) (rhs : Core) :
    StateT SolverState (Except String) Bool := do
  if rhs.freeMetas.contains m then throw "occurs check failed"
  match invert m args rhs with
  | .error _ => pure false
  | .ok solution =>
    modify fun s => { s with subst := (m, solution) :: s.subst }
    pure true

/-- Conservative pattern unification. Same-meta pruning/intersection stays blocked,
    as that part of the Haskell solver is unfinished. This utility does not certify types. -/
private def unifyTerms : Nat → Nat → Core → Core → StateT SolverState (Except String) Bool
  | 0, _, _, _ => throw "unification step limit exceeded"
  | fuel + 1, depth, a, b => do
    let a ← normalOpen depth (← substitute (← get).subst a)
    let b ← normalOpen depth (← substitute (← get).subst b)
    if a == b then return true
    let (ha, xs) := a.unwindApp
    let (hb, ys) := b.unwindApp
    match ha, hb with
    | .mvar m, .mvar n =>
      if m == n then return false
      if ← assign m xs b then return true
      assign n ys a
    | .mvar m, _ => assign m xs b
    | _, .mvar n => assign n ys a
    | _, _ =>
      match a, b with
      | .pi _ a b, .pi _ c d | .sigma _ a b, .sigma _ c d =>
        let dom ← unifyTerms fuel depth a c
        let cod ← unifyTerms fuel (depth + 1) b d
        pure (dom && cod)
      | .lam _ a, .lam _ b => unifyTerms fuel (depth + 1) a b
      | .app a b, .app c d | .pair a b, .pair c d | .cover a b, .cover c d | .sect a b, .sect c d =>
        let first ← unifyTerms fuel depth a c
        let second ← unifyTerms fuel depth b d
        pure (first && second)
      | .fst a, .fst b | .snd a, .snd b => unifyTerms fuel depth a b
      | _, _ =>
        if !(a.freeMetas ++ b.freeMetas).isEmpty then return false
        throw s!"rigid mismatch: {a.pretty} and {b.pretty}"

def solve (equation : Equation) (state : SolverState := {}) : SolverState := Id.run do
  let depth := ((equation.lhs.freeVars ++ equation.rhs.freeVars).map (· + 1)).foldl max 0
  let id := state.nextProblemId
  let start := { state with nextProblemId := id + 1 }
  let (status, result) : ProblemState × SolverState := match unifyTerms 1000 depth equation.lhs equation.rhs start with
    | .ok (true, s) => (.solved, s)
    | .ok (false, s) => (.blocked, s)
    | .error e => (.failed e, start)
  return { result with worklist := result.worklist ++ [⟨id, status, equation⟩] }

def retryBlocked (state : SolverState) : SolverState := Id.run do
  let mut result := { state with worklist := [] }
  for p in state.worklist do
    if p.state == .blocked then
      let next := solve p.equation result
      let updated := next.worklist.getLast!
      result := { next with nextProblemId := result.nextProblemId, worklist := next.worklist.dropLast ++ [{ updated with id := p.id }] }
    else
      result := { result with worklist := result.worklist ++ [p] }
  return result

end Ibis.Unify
