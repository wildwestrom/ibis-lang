import Ibis.Syntax

namespace Ibis.Core

/-- Bottom-up traversal. The depth includes binders introduced by match patterns. -/
partial def rewriteM [Monad m] (f : Nat → Core → m Core) (depth : Nat) (t : Core) : m Core := do
  let t ← match t with
    | .pi n a b => return .pi n (← rewriteM f depth a) (← rewriteM f (depth + 1) b)
    | .lam n b => return .lam n (← rewriteM f (depth + 1) b)
    | .sigma n a b => return .sigma n (← rewriteM f depth a) (← rewriteM f (depth + 1) b)
    | .letE a b => return .letE (← rewriteM f depth a) (← rewriteM f (depth + 1) b)
    | .app a b => return .app (← rewriteM f depth a) (← rewriteM f depth b)
    | .pair a b => return .pair (← rewriteM f depth a) (← rewriteM f depth b)
    | .ann a b => return .ann (← rewriteM f depth a) (← rewriteM f depth b)
    | .fst a => return .fst (← rewriteM f depth a)
    | .snd a => return .snd (← rewriteM f depth a)
    | .matchE a bs => return .matchE (← rewriteM f depth a) (← bs.mapM fun (p, b) => return (p, ← rewriteM f (depth + p.vars.length) b))
    | .cover a b => return .cover (← rewriteM f depth a) (← rewriteM f depth b)
    | .sect a b => return .sect (← rewriteM f depth a) (← rewriteM f depth b)
    | .res a u v p s => return .res (← rewriteM f depth a) (← rewriteM f depth u) (← rewriteM f depth v) (← rewriteM f depth p) (← rewriteM f depth s)
    | .ext a u v p s => return .ext (← rewriteM f depth a) (← rewriteM f depth u) (← rewriteM f depth v) (← rewriteM f depth p) (← rewriteM f depth s)
    | t => pure t
  f depth t

def shift (amount : Nat) (t : Core) : Core := Id.run <| rewriteM (fun depth t => pure <|
  match t with
  | .var n => if n ≥ depth then .var (n + amount) else t
  | _ => t) 0 t

def instantiate (arg body : Core) : Core := Id.run <| rewriteM (fun depth t => pure <|
  match t with
  | .var n => if n == depth then shift depth arg else if n > depth then .var (n - 1) else t
  | _ => t) 0 body

def freeVars (t : Core) : List Nat :=
  let (_, vars) := (rewriteM (m := StateM (List Nat)) (fun depth t => do
    if let .var n := t then
      if n ≥ depth then modify (fun xs => (n - depth) :: xs)
    pure t) 0 t).run []
  vars.eraseDups

def freeMetas (t : Core) : List Nat :=
  let (_, vars) := (rewriteM (m := StateM (List Nat)) (fun _ t => do
    if let .mvar n := t then modify (n :: ·)
    pure t) 0 t).run []
  vars.eraseDups

def unwindApp : Core → Core × List Core
  | .app f x => let (h, xs) := unwindApp f; (h, xs ++ [x])
  | t => (t, [])

end Ibis.Core
