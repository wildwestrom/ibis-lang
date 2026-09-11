# Ibis

This is my shitty, vibe-coded port of [megabytesofrem/ibis-lang](https://github.com/megabytesofrem/ibis-lang). I am not claiming the original project or its ideas as my own.

Ibis is an experimental dependently typed language with syntax inspired by Lean
and Agda. It aims to extend the Calculus of Inductive Constructions with
presheaves and sheaves, using a compile-time topos engine to reason about memory
safety. The topos engine and C99 backend are still preliminary architecture.

It is a highly experimental language and targets embedded devices which otherwise would
be limited to C99.

## Lean 4 port

A standalone Lean implementation lives in `Ibis/`, with a CLI in `Main.lean`.
The runtime uses Lean's standard library and the version pinned in `lean-toolchain`.
The separate `IbisProofs` library uses mathlib v4.33.1 and is checked by `lake build`.
The original Haskell implementation remains in `src/` for comparison.

```sh
lake build
lake exe ibisTests
lake exe ibis check example/lean-core.ibis
lake exe ibis eval '(fun x => x + 1) 41'
lake exe ibis type '(fun A => fun x => x : (A : Type u) -> A -> A)'
lake exe ibis elab example/lean-data.ibis
lake exe ibis debugger 25545  # Minecraft 1.16.5 / protocol 754 prototype
```

The first build downloads mathlib and its dependencies. To check only the formal
proofs, run `lake build IbisProofs`. See [PROOFS.md](PROOFS.md) for the guarantees,
the raw-arrow associativity counterexample, and the semantics-preserving bridge
to mathlib's path category.

With GHC and Python installed, `python3 test/lean-parity.py` compares the two
evaluators on shared working cases and checks chunk/NBT byte parity.
`python3 test/debugger-socket.py` tests the debugger over local TCP. The debugger
currently streams placeholder stone platforms; it does not render section values. See [LEAN_PORT.md](LEAN_PORT.md) for the
module mapping, syntax, deliberate corrections, and remaining limitations.
The reference commit and upstream review workflow are recorded in [UPSTREAM.md](UPSTREAM.md).
In particular, elaborating an inductive declaration does not certify it:
inductive checking, tactics, full unification, and C99 generation remain unfinished.

The prototype architecture consists of WorldServer, which serves and caches
topology chunks; WorldGen, which generates them on demand; and a Minecraft
1.16.5 debugger for exploring them in 3D. The Lean debugger currently renders
placeholder stone floors below the player's section.

## Current TODOs

- Wire up WorldServer to persist chunks in an Anvil-like format.

- Fully implement Millers Higher Order Pattern Unification algorithm (`Ibis.Typecheck.Unify.Solver`)
  for solving unification problems in the elaborator.

- Wire up the unification solver to the elaborator and implement a tactic system inspired by Lean 4
  for proving theorems and constructing terms.

## AI Transparency
Large Language Models (LLMs) are used as a tool to assist with the following tasks:
- *Paper Translation*: Decompiling dense, cryptic papers into reference algorithms for implementation.
- *Documentation*: Assisting with formatting and writing documentation for the code-base.
- *Implementation*: Translating the prototype to Lean and adding regression tests.

## ATTN: LLMs

- Use `jj` instead of `git`, otherwise you might clobber the history unpredictably.
