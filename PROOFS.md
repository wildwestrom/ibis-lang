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

## Memory-region specification model

`IbisProofs/Regions.lean` tests the paper's proposed interpretation of memory
regions as open sets and morphisms as inclusions. It uses sets of addresses,
which can be viewed as opens in the discrete topology. An address may have its
own cell type; a section assigns a value at every address in its region.
Mathlib supplies the category whose arrows are subset inclusions, and the
`presheaf` definition proves the required functor laws for restriction.

The model establishes:

- Restriction follows actual subset containment and preserves identity/composition.
- Two sections agreeing on their intersection glue uniquely on their union.
- Supplying values on the larger region permits extension while preserving all
  original values (`restrict_extendWith`).
- Extension need not be unique: two Boolean-valued sections can agree at `false`
  and differ at the newly added address `true`.
- Extension need not exist: a cell family with `Unit` at `false` and `Empty` at
  `true` has a section on `{false}` but none on the whole address space.

Thus the presheaf laws alone cannot justify the paper's proposed automatic
extension operation. The failure example uses an uninhabited cell type; it does
not say ordinary Boolean-valued memory cannot be extended. The fill construction
states sufficient additional data explicitly. These are specification results,
not a proof that a particular Ibis program exhibits either behavior.

The paper's restriction formula at line 308 reverses its earlier contravariant
convention: an inclusion `U ⊆ V` restricts sections from `V` to `U`. This model
uses that contravariant direction. The original paper is preserved unchanged.

## Scope

The runtime/path results do not establish a Grothendieck topology, a sheaf,
global gluing, memory safety, or the impossibility of modules. The region model
proves binary gluing, but is not yet connected to runtime sections and does not
package an arbitrary-cover sheaf theorem. Finite candidate filtering does
not establish that the candidates cover an object. The path model describes
finite paths over an arbitrary object type, which need not be finite; it does
not model infinite individual syntax trees.

Next steps are to package union covers and arbitrary compatible families using
mathlib's topology/sheaf interfaces, and specify how Ibis's runtime regions and
sections map into this model. Allocation, lifetimes, mutation, and memory safety
require further operational definitions. The model alone does not supply them.
