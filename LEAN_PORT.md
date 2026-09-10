# Lean port

This ports the existing experimental implementation, not the complete language
envisioned in the papers or examples. It is an independent interpreter written
in Lean 4; it does not translate Ibis programs into Lean declarations or use
Lean's kernel to certify Ibis programs. No third-party Lean packages are needed.

## Build and run

Install the toolchain named in `lean-toolchain` using Elan, then run:

```sh
lake build
lake exe ibisTests
python3 test/lean-parity.py  # optional: also requires GHC/runghc and Python 3
python3 test/debugger-socket.py  # Python 3 and local TCP socket access
```

`lake build` builds the library, CLI, and test executable. `ibisTests` runs the
regressions; a parse failure fails a test rather than skipping its assertions.
The parity script compares Lean with the original Haskell evaluator on 13
working cases, plus three byte-for-byte chunk serialization fixtures (including
signed bounds and 64-bit arrow IDs), and three NBT fixtures covering every supported tag. It does not claim parity for unfinished or
erroneous Haskell paths. It uses the original modules directly, avoiding the historical Cabal
test suite's stale `Ibis.Syntax.*` imports and unavailable test dependencies.

Commands return nonzero on errors:

| Command | Behavior |
| --- | --- |
| `lake exe ibis debugger [PORT]` | Run the Minecraft 1.16.5 prototype debugger (default port 25545) |
| `lake exe ibis parse FILE` | Parse a full file and print its surface AST |
| `lake exe ibis elab FILE` | Resolve names and desugar to core declarations |
| `lake exe ibis check FILE` | Check supported definitions sequentially |
| `lake exe ibis eval 'EXPR'` | Normalize a closed, unchecked expression |
| `lake exe ibis type 'EXPR'` | Infer a closed expression's type |

`elab` and `eval` do not imply successful type checking. Like the Haskell
evaluator, evaluation of untyped self-application can diverge. Recursive runtime
operations use Lean's `partial def`; this port supplies no normalization or
type-soundness proof.

## Module mapping

| Haskell modules | Lean module |
| --- | --- |
| `Ibis.AST.Surface`, `Core`, `Operator`, AST display | `Ibis/Syntax.lean` |
| `Ibis.Parser.*` | `Ibis/Parser.lean` |
| `Ibis.Typecheck.Elab`, `ElabCtx` | `Ibis/Elab.lean` |
| `Ibis.Typecheck.Eval` | `Ibis/Eval.lean` |
| `Ibis.Typecheck.Check` | `Ibis/Check.lean` |
| Substitution and free-variable helpers | `Ibis/Core.lean` |
| `Ibis.Typecheck.Unify.*` | `Ibis/Unify.lean` |
| `Category.*`, `Ibis.Compiler.World`, `Ibis.Compiler.WorldGen` | `Ibis/Topology.lean` |
| `Ibis.Compiler.WorldServer` | `Ibis/WorldServer.lean` |
| `Ibis.Compiler.Debugger.*` | `Ibis/Debugger/{NBT,Protocol,Server}.lean` |
| `Data.Serialization` | `Ibis/Serialization.lean` |
| `Ibis.AST.CoAST`, `CFG` | `Ibis/Spatial.lean` |
| `app/Main.hs` | Interpreter and debugger CLI in `Main.lean` |

The Lean port consolidates small modules rather than preserving Haskell module
paths. Errors use `Except String`; closure values store an environment and body
instead of a Haskell function. Indices and levels are nonnegative `Nat`s.
The existing operator spellings are represented as strings in the surface AST.
The unused generic pretty-print state wrapper is replaced by AST rendering.

## Syntax and working examples

`example/lean-core.ibis` checks and `example/lean-data.ibis` elaborates. The older
`embedded.ibis`, `classes.ibis`, and `vect.ibis` contain aspirational syntax and
are not acceptance examples for either implementation.

The parser supports universes, dependent functions and pairs, application,
annotations, lets, literals, operators, lists, conditionals, matches, monadic
desugaring, site primitives, structs, inductives, functions, imports, and tactic
ASTs. Parsing a construct does not imply it can be checked or executed.

```text
def identity (A : Type u) (x : A) : A := x
def increment (x : Int) : Int := x + 1
struct Box (A : Type u) where
  value : A
```

* Universes are `Prop`, `Type 1`, `Type 7`, or `Type u`. `Type 0` is rejected.
  Named universes receive stable numeric levels starting at 1; they are not
  Lean-style universe-polymorphic parameters.
* Lambdas use `fun x y => body` or `λ x => body`.
* Function binders use `(x : A)`. Dependent products use `Σ (x : A), B` or
  `/Sigma (x : A), B`.
* Top-level definitions require a result type and `:=`. Declaration fields and
  constructors occupy separate lines (or use semicolons). Parentheses and lists
  allow line breaks. This is not a full indentation-sensitive layout parser.
* Match branches use `| pattern -> expression`; tuples and constructor patterns
  bind variables from left to right. List partitions use `x :: xs`.
* Do blocks use `do { x <- e; result }` or `do ... end`. Non-final statements
  must be binds, matching the original elaborator's supported desugaring.
* Tactic blocks use `by ... qed`, with newlines or semicolons as separators.
* `Cover u v` and `Sect A u` take atomic arguments; parenthesize compound ones.
  Restriction is `res s to u`; extension is `ext s u -> v`.

The checker provides `Int`, `Nat`, `Float`, `Bool`, `String`, `Unit`, and `Site`.
Integer literals infer `Int`; nonnegative literals also check against `Nat`.
Arithmetic/comparison operators currently operate on `Int`, and Boolean
operators operate on `Bool`. There is no overloaded numeric typeclass machinery.
Other constants can remain symbolic during normalization, but must have a known
signature to pass checking. Definitions are sequential and non-recursive.

## Corrections during translation

The port preserves intended behavior where executable behavior was missing or
inconsistent. Its regression tests explicitly cover:

* Innermost variable index 0, shadowing, and parameter lookup even for uppercase names.
* `Prop` at level 0 and fresh named universes starting at level 1.
* Reserved-word boundaries, Boolean/float/string lexing, comments, whole-input
  parsing, empty tuples, tuple order, and operator precedence.
* Annotation evaluation and checking, let annotations, constant readback,
  constructor applications, list patterns, wildcard patterns, and neutral matches.
* Alpha-insensitive function binder comparison and consistent pattern binding order.
* Function/inductive declaration elaboration and parameterized struct constructors
  with separate projection definitions. Elaborating these is not an inductive proof check.
* Binder-aware substitution and scope inversion, occurs checks under all core
  constructors, lambda wrapping of metavariable solutions, and substitution cycle detection.

## Boundaries inherited from the prototype

* Inductive positivity, recursors, dependent elimination, and general constructor
  pattern checking are unfinished. `check` rejects inductive declarations rather
  than treating unvalidated signatures as proofs. Struct projections can be
  evaluated, but their generated constructor matches cannot yet be checked.
* Tactic ASTs are parsed; tactics, including `sorry`, are not executed or accepted
  as proofs. Imports are parsed but module loading is not implemented.
* Restriction/extension proof synthesis is unimplemented. Core transport can be
  evaluated and checked when supplied with an explicit well-typed proof.
* The unifier is a separate conservative pattern solver. It is not connected to
  elaboration and does not certify equation types. Same-metavariable spine
  intersection/pruning and other unsupported equations remain blocked. A blocked
  equation can be retried after substitutions; it is never reported as solved.
* Presheaf restriction, sieve pullback, finite-cover filtering, chunk generation,
  and agreement checking on overlaps are executable. Arbitrary predicates do not
  certify a Grothendieck topology: `TopologyLaws` makes those obligations explicit.
  Restriction identity/composition and maximal-sieve pullback have Lean proofs.
* Gluing checks overlap agreement and returns the two local sections; it does
  not synthesize a global section. Left Kan extensions are existential containers:
  a contravariant presheaf alone cannot supply a covariant extension operation.
* World generation, chunk lookup, and local section restriction are executable.
  Zero-sized worlds are empty. Chunk serialization matches the upstream binary
  format, but arrow IDs and section payload bytes remain opaque; no world-to-wire
  conversion exists. WorldServer requests run through a closeable channel; generated
  chunks are cached and can be explicitly unloaded. The TCP debugger supports
  protocol 754 status/ping, offline login, escaped system chat, fifteen-second
  keepalives, and horizontal/vertical movement-driven chunk streaming. The view
  requests nearby sections within Y=0–15 and renders the center section as stone,
  independent of section payloads. Multi-section column rendering, authentication,
  automatic cache eviction, and block editing remain unimplemented.
  Socket tests exercise the wire protocol; a real Minecraft client was not tested.
* Spatial ASTs and CFGs are data structures only. Streaming, disk caches, a
  borrow-checking topos engine, and C99 lowering remain unimplemented.

## Reversibility

The Haskell source and Cabal configuration match the reference in `UPSTREAM.md`;
they are refreshed together when the baseline advances. Both builds can coexist:
Lean uses `.lake/`, Haskell uses `dist-newstyle/`. Continue using Cabal to return
to the original implementation; no source or data migration is required.
