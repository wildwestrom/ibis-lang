# Formal proofs

Run `lake build IbisProofs`, or `lake build` to check the proofs alongside the
runtime and test executable. Mathlib is pinned to v4.33.1; the exact dependency
revisions are recorded in `lake-manifest.json`. Runtime modules do not import
mathlib. The proof sources contain no `sorry`, new axioms, or `native_decide`.

## Executable topology guarantees

`IbisProofs/Topology.lean` proves:

- Raw arrow composition has left and right identities.
- Composing arrows restricts sections in the corresponding reverse order.
- Reassociating arrow composition preserves its action on every section.
- Three inclusion arrows give a counterexample to associativity of raw syntax.
- The maximal sieve is closed, and pulling back along identity preserves a sieve.
- Materialization retains exactly the supplied candidates that satisfy the sieve.
- With lawful Boolean equality, overlap checking succeeds exactly when the two
  restrictions agree.
- Chunk generation succeeds exactly when the site's predicate accepts the sieve
  and the result contains the specified coordinate, filtered candidates, and payload.

## Mathlib path model

`IbisProofs/Paths.lean` interprets inclusion arrows as edges of a quiver and uses
mathlib's `CategoryTheory.Paths` to obtain a category of finite paths. Each edge
retains its source, target, and local position. The translation removes identity
steps and composition parentheses; it does not impose additional geometric laws.

The proofs establish that translation preserves composition, that reassociated
compositions translate to equal paths, and that interpreting a translated path
gives exactly the existing `restrictSection` result. Consequently, equal paths
act identically on every section. This provides a lawful mathematical model
without changing the runtime's representation or its structural comparisons.

## Scope

These results do not establish a Grothendieck topology, a sheaf, global gluing,
memory safety, or the impossibility of modules. Finite candidate filtering does
not establish that the candidates cover an object. The path model describes
finite paths over an arbitrary object type, which need not be finite; it does
not model infinite individual syntax trees.

The next mathematical step is to define a specific covering rule on the path
category and prove mathlib's Grothendieck topology axioms for that rule. Such a
rule must be motivated by Ibis's intended semantics rather than chosen merely
because its axioms are easy to prove.
