import Std

namespace Ibis

inductive Literal where
  | int : Int → Literal
  | float : Float → Literal
  | bool : Bool → Literal
  | string : String → Literal
  deriving Repr, BEq, Inhabited

inductive Pat where
  | lit : Literal → Pat
  | capture : String → Pat
  | wildcard
  | tuple : List Pat → Pat
  | ctor : String → List Pat → Pat
  | partition : String → Pat → Pat
  deriving Repr, BEq, Inhabited

def Pat.vars : Pat → List String
  | .capture n => [n]
  | .tuple ps | .ctor _ ps => ps.flatMap Pat.vars
  | .partition n p => (if n == "_" then [] else [n]) ++ p.vars
  | _ => []

inductive Universe where
  | named : String → Universe
  | level : Nat → Universe
  deriving Repr, BEq

inductive Term where
  | universe : Universe → Term
  | const : String → Term
  | mvar : Nat → Term
  | var : String → Term
  | lit : Literal → Term
  | unit
  | pi : String → Term → Term → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  | sigma : String → Term → Term → Term
  | pair : Term → Term → Term
  | fst : Term → Term
  | snd : Term → Term
  | letE : String → Option Term → Term → Term → Term
  | ann : Term → Term → Term
  | unop : String → Term → Term
  | binop : String → Term → Term → Term
  | list : List Term → Term
  | ifE : Term → Term → Term → Term
  | forE : String → Term → Term → Term
  | matchE : Term → List (Pat × Term) → Term
  | doE : List Term → Term
  | bind : String → Term → Term
  | site : String → Term
  | cover : Term → Term → Term
  | sect : Term → Term → Term
  | res : Term → Term → Term
  | ext : Term → Term → Term → Term
  deriving Repr, BEq, Inhabited

inductive Tactic where
  | intro : String → Tactic
  | exact : Term → Tactic
  | apply : Term → Tactic
  | rfl
  | simp : Term → Tactic
  | cases : Term → Tactic
  | induction : Term → Tactic
  | bind : String → Option Term → Term → Tactic
  | haveE : String → Option Term → Term → Tactic
  | showE : Term → Tactic
  | admit
  | pathAcross : Term → Term → Tactic
  | covers : Term → Term → Tactic
  | res : Term → Term → Tactic
  | lan : Term → Term → Tactic
  | glue : Term → Term → Term → Term → Tactic
  deriving Repr, BEq

abbrev Param := String × Term

inductive FunctionBody where
  | simple : Term → FunctionBody
  | tactics : List Tactic → FunctionBody
  deriving Repr, BEq

structure CoverRule where
  parent : String
  children : List String
  deriving Repr, BEq

inductive Decl where
  | term : Term → Decl
  | struct : String → List Param → List Param → Decl
  | inductiveE : String → List Param → Term → List Param → Decl
  | function : String → List Param → Term → FunctionBody → Decl
  | site : String → List CoverRule → Decl
  | importE : String → Option String → Decl
  | importExposing : String → List String → Decl
  deriving Repr, BEq

inductive Core where
  | universe : Nat → Core
  | const : String → Core
  | mvar : Nat → Core
  | var : Nat → Core
  | lit : Literal → Core
  | unit
  | pi : Option String → Core → Core → Core
  | lam : Option String → Core → Core
  | app : Core → Core → Core
  | sigma : Option String → Core → Core → Core
  | pair : Core → Core → Core
  | fst : Core → Core
  | snd : Core → Core
  | letE : Core → Core → Core
  | ann : Core → Core → Core
  | matchE : Core → List (Pat × Core) → Core
  | site : Nat → Core
  | cover : Core → Core → Core
  | sect : Core → Core → Core
  | res : Core → Core → Core → Core → Core → Core
  | ext : Core → Core → Core → Core → Core → Core
  deriving Repr, BEq, Inhabited

inductive CoreDecl where
  | defn : String → Core → Core → CoreDecl
  | inductiveE : String → Core → List (String × Core) → CoreDecl
  deriving Repr, BEq

def Literal.pretty : Literal → String
  | .int n => toString n
  | .float n => toString n
  | .bool b => if b then "true" else "false"
  | .string s => reprStr s

def Pat.pretty : Pat → String
  | .lit l => l.pretty
  | .capture n => n
  | .wildcard => "_"
  | .tuple ps => "(" ++ String.intercalate ", " (ps.map Pat.pretty) ++ ")"
  | .ctor n ps => "(" ++ String.intercalate " " (n :: ps.map Pat.pretty) ++ ")"
  | .partition n p => "(" ++ n ++ " :: " ++ p.pretty ++ ")"

partial def Core.pretty : Core → String
  | .universe n => if n == 0 then "Prop" else s!"Type {n}"
  | .const n => n
  | .mvar n => s!"?{n}"
  | .var n => s!"#{n}"
  | .lit l => l.pretty
  | .unit => "()"
  | .pi n a b => s!"(({n.getD "_"} : {a.pretty}) -> {b.pretty})"
  | .lam n b => s!"(fun {n.getD "_"} => {b.pretty})"
  | .app f x => s!"({f.pretty} {x.pretty})"
  | .sigma n a b => s!"(Σ ({n.getD "_"} : {a.pretty}), {b.pretty})"
  | .pair a b => s!"({a.pretty}, {b.pretty})"
  | .fst p => s!"(fst {p.pretty})"
  | .snd p => s!"(snd {p.pretty})"
  | .letE e b => s!"(let _ = {e.pretty} in {b.pretty})"
  | .ann e t => s!"({e.pretty} : {t.pretty})"
  | .matchE e bs => "(match " ++ e.pretty ++ " with " ++
      String.intercalate " " (bs.map fun (p, b) => "| " ++ p.pretty ++ " -> " ++ b.pretty) ++ ")"
  | .site n => s!"@#{n}"
  | .cover u v => s!"(Cover {u.pretty} {v.pretty})"
  | .sect a u => s!"(Sect {a.pretty} {u.pretty})"
  | .res a u v p s => s!"(res {a.pretty} {u.pretty} {v.pretty} {p.pretty} {s.pretty})"
  | .ext a u v p s => s!"(ext {a.pretty} {u.pretty} {v.pretty} {p.pretty} {s.pretty})"

def CoreDecl.pretty : CoreDecl → String
  | .defn n t b => s!"def {n} : {t.pretty} := {b.pretty}"
  | .inductiveE n t cs => s!"inductive {n} : {t.pretty} where\n" ++
      String.intercalate "\n" (cs.map fun (c, ty) => s!"  {c} : {ty.pretty}")

end Ibis
