import Ibis

open Ibis

private def require (label : String) (condition : Bool) : Except String Unit :=
  if condition then pure () else throw label
private def rejects (label : String) (result : Except String α) : Except String Unit :=
  match result with | .error _ => pure () | .ok _ => throw s!"{label}: unexpectedly succeeded"
private def core (s : String) : Except String Core := do elaborate (← Parser.parseExpr s)
private def norm (s : String) : Except String Core := do normalize (← core s)
private def decls (s : String) : Except String (List CoreDecl) := do elaborateProgram (← Parser.parseProgram s)

private def cases : List (String × Except String Unit) := [
  ("named universes start at one", do
    require "Type u" ((← core "Type u") == .universe 1)
    require "stable name" ((← core "(Type u, Type u, Type v)") ==
      .pair (.universe 1) (.pair (.universe 1) (.universe 2)))),
  ("numeric universes and Prop", do
    require "Type 7" ((← core "Type 7") == .universe 7)
    require "Prop" ((← core "Prop") == .universe 0)
    rejects "Type zero" (Parser.parseExpr "Type 0")
    rejects "negative level" (Parser.parseExpr "Type -1")),
  ("lexer boundaries and literals", do
    require "bool" ((← norm "true") == .lit (.bool true))
    require "float" ((← norm "12.25") == .lit (.float 12.25))
    require "string" ((← norm "\"a\\n\\\"b\"") == .lit (.string "a\n\"b"))
    require "keyword prefix" ((← Parser.parseExpr "Typewriter") == .const "Typewriter")
    require "nested comments" ((← norm "{- a {- b -} c -} 1 -- tail") == .lit (.int 1))
    rejects "unterminated comment" (Parser.parseExpr "{-")
    rejects "unterminated string" (Parser.parseExpr "\"bad")
    rejects "trailing junk" (Parser.parseExpr "1 ; 2")),
  ("operator precedence", do
    require "multiply first" ((← norm "1 + 2 * 3") == .lit (.int 7))
    require "left associative subtraction" ((← norm "10 - 3 - 2") == .lit (.int 5))
    require "negative argument" ((← norm "-2 * 3") == .lit (.int (-6)))
    require "comparison" ((← norm "2 <= 3 and not false") == .lit (.bool true))
    rejects "nonassociative comparison" (Parser.parseExpr "1 < 2 < 3")
    rejects "division by zero" (norm "1 / 0")),
  ("tuple order and unit", do
    require "pair" ((← norm "(1, 2)") == .pair (.lit (.int 1)) (.lit (.int 2)))
    require "unit" ((← norm "()") == .unit)
    require "fst" ((← norm "fst (1, 2)") == .lit (.int 1))
    require "snd" ((← norm "snd (1, 2)") == .lit (.int 2))
    rejects "bad projection" (norm "fst 1")),
  ("binding and shadowing", do
    require "innermost index" ((← core "fun x => fun y => x") == .lam (some "x") (.lam (some "y") (.var 1)))
    require "beta" ((← norm "(fun x => fun y => x) 11 22") == .lit (.int 11))
    require "shadow" ((← norm "let x = 1 in let x = 2 in x") == .lit (.int 2))
    require "capture avoidance" ((← norm "fun x => (fun y => fun z => y) x") == .lam none (.lam none (.var 1)))
    rejects "unbound" (core "x")
    rejects "scope does not leak" (core "(fun x => x, x)")),
  ("annotations and dependent types", do
    require "annotation evaluation" ((← norm "(1 : Int)") == .lit (.int 1))
    let identity ← core "(fun A => fun x => x : (A : Type u) -> (x : A) -> A)"
    let _ ← inferType identity
    let sig ← core "((1, true) : Σ (x : Int), Bool)"
    let _ ← inferType sig
    require "universe inference" ((← inferType (← core "Type 7")) == .universe 8)
    rejects "type mismatch" (inferType (← core "(true : Int)"))
    rejects "let annotation" (inferType (← core "let x : Bool = 1 in x"))
    rejects "untyped lambda" (inferType (← core "fun x => x"))),
  ("pattern binding order", do
    require "tuple captures" ((← norm "match (1, 2) with | (x, y) -> x - y") == .lit (.int (-1)))
    require "constructor captures" ((← norm "match Some 7 with | Some x -> x") == .lit (.int 7))
    require "list partition" ((← norm "match [1, 2] with | x :: xs -> x") == .lit (.int 1))
    require "wildcard" ((← norm "match 3 with | _ -> 4") == .lit (.int 4))
    rejects "duplicate capture" (core "match (1, 2) with | (x, x) -> x")
    rejects "non-exhaustive" (norm "match 3 with | 2 -> 4")),
  ("neutral match readback", do
    let n ← norm "fun x => match x with | (a, b) -> a"
    require "branch binder levels" (n == .lam none (.matchE (.var 0)
      [(.tuple [.capture "a", .capture "b"], .var 1)]))),
  ("do and for desugaring", do
    let t ← core "do { x <- 1; x }"
    require "bind" (t == .app (.app (.const ">>=") (.lit (.int 1))) (.lam (some "x") (.var 0)))
    let _ ← core "for x in [1, 2] do x"
    rejects "empty do" (core "do {}")
    rejects "final bind" (core "do { x <- 1 }")
    rejects "missing do close" (Parser.parseExpr "do { x <- 1")),
  ("function declarations and globals", do
    let ds ← decls "def id (A : Type u) (x : A) : A := x\ndef n : Int := id Int 42"
    let ctx ← checkProgram ds
    require "global evaluation" ((← normalize (.const "n") ctx.globals) == .lit (.int 42))
    rejects "bad definition" (do checkProgram (← decls "def n : Bool := 1"))
    rejects "duplicate" (decls "def n : Int := 1\ndef n : Int := 2")
    rejects "unknown constant" (do checkProgram (← decls "def n : Int := Missing"))),
  ("structures and projections", do
    let ds ← decls "struct Point where\n  x : Int\n  y : Int"
    require "inductive plus projections" (ds.length == 3)
    let globals := ds.filterMap fun d => match d with | .defn n _ b => some (n, b) | _ => none
    require "projection" ((← normalize (.app (.const "Point_x")
      (.app (.app (.const "Point_mk") (.lit (.int 10))) (.lit (.int 20)))) globals) == .lit (.int 10))
    let ds ← decls "struct Box (A : Type u) where\n  value : A"
    require "parameterized struct" (ds.length == 2)
    match (ds[1]? : Option CoreDecl) with
    | some (.defn _ ty _) => require "parameter projection type" (ty ==
        .pi (some "A") (.universe 1) (.pi (some "self") (.app (.const "Box") (.var 0)) (.var 1)))
    | _ => throw "missing Box projection"),
  ("inductive constructors", do
    let ds ← decls "inductive Vect (A : Type u) : Nat -> Type u where\n  Nil : Vect A 0\n  Cons : (n : Nat) -> A -> Vect A n -> Vect A n"
    match ds with
    | [.inductiveE "Vect" _ cs] => require "constructors" (cs.map Prod.fst == ["Nil", "Cons"])
    | _ => throw "expected Vect inductive"),
  ("unsupported features are explicit", do
    rejects "restriction synthesis" (core "fun s => res s to s")
    rejects "extension synthesis" (core "fun s => ext s s -> s")
    let d ← Parser.parseDecl "def p : Prop := by\n  intro x\n  exact x\nqed"
    rejects "tactic execution" (elaborateProgram [d])
    let d ← Parser.parseDecl "import Data.List as L"
    rejects "module loading" (elaborateProgram [d])
    rejects "aspirational syntax" (Parser.parseProgram "class Show where")),
  ("topological core evaluation", do
    require "cover" ((← elaborateProgram (← Parser.parseProgram "site S where\n cover @U has {@V}\nCover @U @V")).length == 1)
    require "transport" ((← normalize (.res (.const "Int") (.site 0) (.site 1) (.const "proof") (.lit (.int 8)))) == .lit (.int 8))
    let term := Core.lam none (.ext (.const "Int") (.site 0) (.site 1) (.const "proof") (.var 0))
    require "neutral transport" ((← normalize term) == term)
    rejects "unproved transport" (inferType (.res (.const "Int") (.site 0) (.site 1) (.unit) (.lit (.int 8))))),
  ("capture-avoiding substitution", do
    require "under binder" (Core.instantiate (.var 0) (.lam none (.var 1)) == .lam none (.var 1))
    require "free variables" ((Core.lam none (.pair (.var 0) (.var 2))).freeVars == [1])
    require "topological metas" ((Core.res (.mvar 7) (.site 0) (.site 1) (.mvar 8) (.mvar 9)).freeMetas.length == 3)),
  ("pattern unification", do
    let rhs := Core.pair (.var 1) (.var 0)
    let solution ← Unify.invert 0 [.var 1, .var 0] rhs
    require "lambda solution" (solution == .lam none (.lam none (.pair (.var 1) (.var 0))))
    rejects "occurs" (Unify.invert 0 [] (.app (.const "F") (.mvar 0)))
    rejects "nonlinear" (Unify.invert 0 [.var 0, .var 0] (.var 0))
    rejects "escape" (Unify.invert 0 [.var 0] (.var 1))
    let solved := Unify.solve ⟨.universe 1, .app (.mvar 0) (.var 0), .var 0⟩
    require "solved" (solved.worklist.head?.any (fun p => p.state == .solved))
    let blocked := Unify.solve ⟨.universe 1, .app (.mvar 0) (.var 0), .app (.mvar 0) (.var 1)⟩
    require "intersection blocked" (blocked.worklist.head?.any (fun p => p.state == .blocked))
    rejects "cyclic substitutions" (Unify.substitute [(0, .mvar 1), (1, .mvar 0)] (.mvar 0))),
  ("finite covers and gluing", do
    let site : Topology.GrothendieckSite Nat := ⟨⟨fun _ => true⟩⟩
    let sieve : Topology.Sieve Nat 0 := ⟨fun a => match a with | .id => true | _ => false⟩
    let candidates : List (Topology.CoveringArrow Nat 0) := [⟨0, .id⟩, ⟨1, .inclusion ⟨1, 2, 3⟩⟩]
    let chunk ← Topology.generateChunk site ⟨3, 7, 2⟩ (.base (42 : Nat)) candidates sieve
    require "filtered cover" (chunk.coverage.arrows.length == 1 && chunk.coverage.depth == 7)
    let badSite : Topology.GrothendieckSite Nat := ⟨⟨fun _ => false⟩⟩
    rejects "invalid cover" (Topology.generateChunk badSite ⟨0, 0, 0⟩ (.base (0 : Nat)) candidates sieve)
    let p : Topology.Presheaf Nat := ⟨fun _ => Nat, fun _ x => x⟩
    require "agreement" ((Topology.glue p (u := 0) (v := 1) (w := 2) (.inclusion ⟨0, 0, 0⟩) (.inclusion ⟨0, 0, 0⟩) 3 3).isSome)
    require "disagreement" ((Topology.glue p (u := 0) (v := 1) (w := 2) (.inclusion ⟨0, 0, 0⟩) (.inclusion ⟨0, 0, 0⟩) 3 4).isNone)),
  ("world generation and local sections", do
    let site : Topology.GrothendieckSite Nat := ⟨⟨fun _ => true⟩⟩
    let world ← Topology.generateWorld (c := 0) (Val := Nat) site (2, 2, 2)
    require "coordinate order" (world.chunks.map (·.coord) ==
      [⟨0, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, 1, 0⟩, ⟨0, 1, 1⟩,
       ⟨1, 0, 0⟩, ⟨1, 0, 1⟩, ⟨1, 1, 0⟩, ⟨1, 1, 1⟩])
    require "empty sections and covers" (world.chunks.all fun chunk =>
      chunk.coverage.depth == Int.ofNat chunk.coord.y.toNat && chunk.coverage.arrows.isEmpty &&
        match chunk.payload with | .empty => true | _ => false)
    require "missing chunk" ((Topology.chunkAt world ⟨2, 0, 0⟩).isNone)
    let pos : Spatial.LocalPos := ⟨1, 2, 3⟩
    match Topology.sectionIn world ⟨1, 1, 1⟩ (Topology.localRestriction (target := 1) pos) with
    | some (.restrict (.inclusion p) .empty) => require "position preserved" (p == pos)
    | _ => throw "expected restricted empty section"
    require "missing section" ((Topology.sectionIn world ⟨9, 0, 0⟩ (.id)).isNone)
    for size in [(0, 2, 2), (2, 0, 2), (2, 2, 0), (4294967295, 0, 1)] do
      require "zero dimension" ((← Topology.generateWorld (c := 0) (Val := Nat) site size).chunks.isEmpty)
    let badSite : Topology.GrothendieckSite Nat := ⟨⟨fun _ => false⟩⟩
    rejects "world cover" (Topology.generateWorld (c := 0) (Val := Nat) badSite (1, 1, 1))
    let a : Topology.Arrow Nat 0 1 := .inclusion pos
    require "same arrow" ((Topology.eqArrow a a).isSome)
    require "different position" ((Topology.eqArrow a (.inclusion (v := 1) ⟨1, 2, 4⟩)).isNone)
    require "different target" ((Topology.eqArrow a (.inclusion (v := 2) pos)).isNone)
    let composed : Topology.Arrow Nat 0 2 := Topology.localComposition 1 pos ⟨4, 5, 6⟩
    match Topology.restrictSection composed (.base (42 : Nat)) with
    | .restrict (.inclusion p) (.restrict (.inclusion q) (.base n)) =>
      require "composition order" (p == pos && q == ⟨4, 5, 6⟩ && n == 42)
    | _ => throw "expected composed restriction"),
  ("chunk wire format", do
    let chunk : Serialization.SerializedChunk := ⟨-1, 2, -3, 4, #[0x0102030405060708], ⟨#[0, 255]⟩⟩
    let bytes ← Serialization.serializeChunk chunk
    let expected : ByteArray := ⟨#[73, 66, 73, 83, 255, 255, 255, 255,
      2, 0, 0, 0, 253, 255, 255, 255, 4, 0, 0, 0, 1, 0, 0, 0,
      8, 7, 6, 5, 4, 3, 2, 1, 2, 0, 0, 0, 0, 255]⟩
    require "little-endian layout" (bytes == expected)
    require "decode golden bytes" ((← Serialization.deserializeChunk expected) == chunk)
    require "trailing bytes match upstream" ((← Serialization.deserializeChunk (bytes ++ ⟨#[99]⟩)) == chunk)
    for i in [:bytes.size] do
      rejects "truncated chunk" (Serialization.deserializeChunk (bytes.extract 0 i))
    rejects "bad magic" (Serialization.deserializeChunk (bytes.set! 0 0))
    let oversized := (((bytes.set! 20 255).set! 21 255).set! 22 255).set! 23 255
    rejects "oversized arrow count" (Serialization.deserializeChunk oversized)
    let oversized := (((bytes.set! 32 255).set! 33 255).set! 34 255).set! 35 255
    rejects "oversized payload" (Serialization.deserializeChunk oversized))
]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, test) in cases do
    match test with
    | .ok _ => IO.println s!"PASS {name}"
    | .error e => IO.println s!"FAIL {name}: {e}"; failures := failures + 1
  IO.println s!"{cases.length - failures}/{cases.length} groups passed"
  pure (if failures == 0 then 0 else 1)
