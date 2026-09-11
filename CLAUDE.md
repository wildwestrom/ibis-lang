# Ibis — Lean 4 port

A fork/port of [megabytesofrem/ibis-lang](https://github.com/megabytesofrem/ibis-lang)
(original is not ours — see `UPSTREAM.md`). Ibis is an experimental dependently
typed language extending CIC with presheaves and sheaves, using a compile-time
topos engine to reason about memory safety. Targets embedded devices otherwise
stuck on C99.

Live per-session numbers (file inventory, theorem lists, `sorry` scan, working-copy
state, build freshness) are injected automatically by `.claude/context-digest.py`
via a `SessionStart` hook. **Trust that digest instead of re-deriving it.** Re-run
`python3 .claude/context-digest.py` after changing files. What follows is only the
part that does not change.

## Version control: jj, not git

This repo is colocated (`.git` + `.jj`). **Use `jj` for anything that mutates
history** — `git` commands can clobber it unpredictably. `git log`/`git show` are
fine for reading.

- `jj st`, `jj diff`, `jj log` — inspect
- `jj commit -m "..."`, `jj bookmark set main -r @-`, `jj git push` — record
- `jj file untrack <path>` — stop tracking
- `.claude/` is selectively ignored: `context-digest.py` and `settings.json` are
  tracked as shared tooling; `settings.local.json` and everything else is not.
  The ignore rule is `.claude/*` (contents), **not** `.claude/` (directory) —
  git cannot re-include a path beneath an excluded directory, so the trailing
  slash would turn the negations into silent no-ops.

## Build and test

Mathlib is pinned to **v4.33.1**, matching `lean-toolchain`; exact dependency
revisions live in `lake-manifest.json`.

```sh
timeout 590 lake build IbisProofs   # proofs only
timeout 590 lake build              # proofs + runtime + tests
timeout 590 lake exe ibisTests
lake exe ibis check example/lean-core.ibis
lake exe ibis eval '(fun x => x + 1) 41'
lake exe ibis debugger 25545        # Minecraft 1.16.5 / protocol 754
```

Builds are slow — always wrap in `timeout 590` (already in the permission
allowlist, so those exact forms don't prompt). The first build downloads mathlib.
Dev shell comes from `flake.nix` via direnv.

`python3 test/lean-parity.py` compares the Lean and Haskell evaluators on shared
cases and checks chunk/NBT byte parity; `python3 test/debugger-socket.py` tests
the debugger over local TCP.

## Layout

- `Ibis/` — the Lean runtime. **Does not import mathlib.** Parser → Syntax →
  Elab → Check → Eval, plus `Topology.lean`/`Spatial.lean` (the topos/chunk
  engine), `WorldServer.lean`, `Debugger/`.
- `IbisProofs/` — the proof library, mathlib-backed. Separate `lean_lib`.
- `src/`, `app/` — the original Haskell implementation, kept for comparison.
- `paper/ibis_semantics.tex` — the spec the proofs are held against.
- `example/*.ibis`, `Tests.lean`, `test/` — examples and tests.

## The single most important framing

**The proofs are about specification models, not certification of the runtime.**
Implementing the interpreter in Lean does not certify it. Do not describe the
runtime as verified, memory-safe, or proven correct.

- `IbisProofs/Regions.lean` / `RegionSheaf.lean` model regions as address sets
  (opens in the discrete topology) and prove the presheaf/sheaf laws *of that
  model*.
- `IbisProofs/RegionBridge.lean` is a **conditional** bridge: it requires
  evidence of subset containment as a hypothesis. The implementation does not
  yet produce that evidence, so it cannot certify the checker's `res`/`ext` uses.
- Raw `Ibis.Topology.Arrow` composition is **not associative** — that's proved as
  a counterexample (`Arrow.compose_not_associative`). Associativity holds only
  after translating into mathlib's path category (`IbisProofs/Paths.lean`), which
  quotients out identity steps and parenthesization.
- `SiteTopology.isCover` is only a Boolean predicate, not a Grothendieck topology.
- Elaborating an inductive declaration does **not** check it.

`PROOF_ROADMAP.md` holds the gap table with explicit completion conditions;
`PROOFS.md` states what is actually proved and under which assumptions. Keep both
current when adding proofs, and keep their claims narrow.

Convention gotcha: an inclusion `U ⊆ V` induces `F(V) → F(U)` (restriction is
contravariant). The paper's "Restriction Maps" section reverses its own earlier
convention — follow the contravariant one.

## Proof hygiene

`IbisProofs/` must stay free of `sorry`, `admit`, new `axiom`s, and
`native_decide` — `PROOFS.md` claims their absence. A `UserPromptSubmit` hook
re-scans the proof library on every prompt (`--check-proofs`, ~30ms) and stays
silent unless something regressed, so a stub introduced mid-session surfaces
immediately rather than at next session start. If you cannot close a goal, say
so and leave the theorem unstated rather than stubbing it.

Note that Ibis-the-language has its own `sorry`/`admit` *tactic tokens* in
`Ibis/Syntax.lean` and `Ibis/Parser.lean`. Those are source-language keywords,
not Lean escape hatches — leave them alone.

## Unfinished, in rough priority order

- Wire `WorldServer` to persist chunks in an Anvil-like format.
- Finish Miller's higher-order pattern unification (`Ibis/Unify.lean`) and
  connect the solver to the elaborator.
- A Lean-4-inspired tactic system for proving theorems and constructing terms.
- Inductive checking and C99 generation.
- The debugger streams placeholder stone floors below the player's section; it
  does not render section values.

## Attribution

`README.md` carries an AI-transparency section — LLMs are used for paper
translation, docs, and the Lean port plus regression tests. Keep it accurate.
