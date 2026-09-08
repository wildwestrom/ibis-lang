# Haskell upstream

The Lean implementation follows the behavior of
[megabytesofrem/ibis-lang](https://github.com/megabytesofrem/ibis-lang).

## Baseline

- Reference commit: `8465642e6e5044ea7572499aa98399621d9a8087`
- Commit subject: `Scaffold world gen`
- Last checked against `upstream/main`: 2026-09-09
- The Haskell files in `src/` match this commit.

This identifies the source used for the port, not a claim of complete behavioral
equivalence. Corrections and unfinished features are documented in
[LEAN_PORT.md](LEAN_PORT.md). The parity tests cover shared working evaluator cases.

## Remotes

- `upstream`: `https://github.com/megabytesofrem/ibis-lang.git`
- `origin` currently points to the Haskell fork, `git@github.com:wildwestrom/ibis-lang.git`.

The proposed independent home is `wildwestrom/ibis-lean`; it has not been created
as part of this setup. When it exists, rename the current `origin` to
`haskell-fork` and add the new repository as `origin`.

## Following changes with Jujutsu

```sh
jj git fetch --remote upstream
jj log -r '8465642e6e5044ea7572499aa98399621d9a8087..main@upstream'
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
