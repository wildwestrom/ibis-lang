# Haskell upstream

The Lean implementation follows the behavior of
[megabytesofrem/ibis-lang](https://github.com/megabytesofrem/ibis-lang).

## Baseline

- Reference commit: `4b5194ac2dcb89d894d31f9d5b3bb20af2261d0c`
- Commit subject: `Chunk serialization`
- Last checked against `upstream/main`: 2026-09-09
- The Haskell files in `src/` match this commit.

This identifies the source used for the port, not a claim of complete behavioral
equivalence. Corrections and unfinished features are documented in
[LEAN_PORT.md](LEAN_PORT.md). The parity tests cover shared working evaluator cases
and chunk wire-format fixtures.

## Remotes

- `upstream`: `https://github.com/megabytesofrem/ibis-lang.git`
- `origin` currently points to the Haskell fork, `git@github.com:wildwestrom/ibis-lang.git`.

The proposed independent home is `wildwestrom/ibis-lean`; it has not been created
as part of this setup. When it exists, rename the current `origin` to
`haskell-fork` and add the new repository as `origin`.

## Following changes with Jujutsu

```sh
jj git fetch --remote upstream
jj log -r '4b5194ac2dcb89d894d31f9d5b3bb20af2261d0c..main@upstream'
```

Keep `main@upstream` untracked in Jujutsu so fetching Haskell changes does not
automatically move or merge into the local Lean `main` bookmark. The remote
bookmark remains available for inspection after fetching.

Review each upstream change, translate relevant behavior, and add regression or
parity tests. Update the pinned Haskell reference and this baseline together
after running `lake build`, `lake exe ibisTests`, and
`python3 test/lean-parity.py`. Record any deferred changes explicitly; fetching
alone does not advance the port's baseline. Upstream commits should not be
automatically merged into the Lean implementation.

## Ported through `4b5194ac`

The Haskell snapshot, Cabal configuration, and `example/vect.ibis` match the
reference. Lean now supports the chunk wire record, empty sections,
position-bearing inclusions, world/region records, chunk lookup, local section
restriction, and initial world generation. `LocalCoord` and `VoxelChunk` remain
aliases for the renamed Lean types. Chunk generation now takes `Spatial.ChunkPos`
(unsigned 32-bit coordinates), following upstream.

Intentional differences:

- Zero in any world dimension produces no chunks instead of unsigned underflow.
- Invalid covers return `Except.error` rather than throwing a runtime exception.
- Arrow path comparison does not imply object equality. `eqArrow` checks target
  equality using `DecidableEq`; it does not reproduce upstream's `unsafeCoerce`.
  `localComposition` takes the intermediate object explicitly.
- Serialization rejects lengths that do not fit the 32-bit format. Decoding
  validates lengths against available bytes before allocating; trailing bytes
  are ignored, matching upstream. The signed wire coordinates are separate from
  unsigned spatial coordinates; no automatic conversion is introduced.

Deferred: `WorldServer`'s STM request/queue scaffold (upstream has no processing
loop), and the aspirational list/site syntax added to `vect.ibis`. Serialization
stores opaque arrow IDs and section bytes; connecting them to live world data
is not implemented upstream or in Lean.

Validation: `lake build`, `lake exe ibisTests` (20 groups), and
`python3 test/lean-parity.py` (13 evaluator and 3 chunk-format comparisons) passed.
