# Formal proofs

Run `lake build IbisProofs`, or `lake build` to check the proofs alongside the
runtime and test executable. Mathlib is pinned to v4.33.1; the exact dependency
revisions are recorded in `lake-manifest.json`. Runtime modules do not import
mathlib. The proof sources contain no `sorry`, new axioms, or `native_decide`.

See [PROOF_ROADMAP.md](PROOF_ROADMAP.md) for the remaining gaps, paper references,
and explicit completion conditions.

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
- Arbitrary indexed compatible families glue uniquely over their union,
  including the empty family over the empty region (`existsUnique_glue_iUnion`).
- Supplying values on the larger region permits extension while preserving all
  original values (`restrict_extendWith`).
- `extendNew` is executable when old-region membership is decidable and only
  asks for initialization values on the difference `V \ U`. Restriction recovers
  both the old section and the supplied new values. Such initialization is
  necessary and sufficient for an extension (`extension_exists_iff`). Two
  executable `#guard` checks exercise preservation and initialization separately.
- Extension need not be unique: two Boolean-valued sections can agree at `false`
  and differ at the newly added address `true`.
- Extension need not exist: a cell family with `Unit` at `false` and `Empty` at
  `true` has a section on `{false}` but none on the whole address space.

Thus the presheaf laws alone cannot justify the paper's proposed automatic
extension operation. The failure example uses an uninhabited cell type; it does
not say ordinary Boolean-valued memory cannot be extended. The fill construction
states sufficient additional data explicitly. These are specification results,
not a proof that a particular Ibis program exhibits either behavior.

The paper's “Restriction Maps” formula reverses its earlier contravariant
convention: an inclusion `U ⊆ V` restricts sections from `V` to `U`. This model
uses that contravariant direction. The original paper is preserved unchanged.

## Bridge to executable topology sections

`IbisProofs/RegionBridge.lean` interprets the existing `Ibis.Topology.Section`
datatype in the region model. A supplied map assigns address regions to runtime
objects. `ValidArrow` requires actual subset evidence at every inclusion,
including intermediate steps; `ValidSection` requires it for all stored
restrictions. An inclusion between distinct singleton regions is proved invalid.

Empty sections denote `none` at every address; base sections denote a constant
`some value`. The proofs establish that executable `restrictSection` preserves
validity and commutes with address-level restriction. This is a conditional
semantic bridge, not an enforcement mechanism: runtime constructors still accept
arbitrary indices, and site declarations do not yet produce the required evidence.
The interpretation forgets local position labels and is not claimed to be faithful.
Absent values are not evidence of initialized memory. This bridge concerns the
topology datatype, not the interpreter's separate `Core` and `Value` datatypes.

## Lawful region site and sheaf

`IbisProofs/RegionSheaf.lean` packages the model in mathlib's actual
`GrothendieckTopology` and `Sheaf` interfaces. Covering sieves are characterized
by every address belonging to one of their source regions. Because all subsets
are regions, singleton regions provide a basis; maximality, pullback stability,
and local character are proved. An empty sieve covers exactly the empty region.

`presheaf_isSheaf` proves unique amalgamation for arbitrary covering sieves of
dependent address-valued sections, and `regionSheaf` packages the result. This
establishes a sheaf for the address-region specification, not for the runtime's
unvalidated Boolean coverage predicates or its overlap-checking `glue` function.

## Scope

The region specification now has a lawful site, full sheaf theorem, and a
conditional bridge to executable topology restriction. None of these establishes
memory safety or the impossibility of modules. Finite candidate filtering still
does not establish that the candidates cover an object. The path model describes
finite paths over an arbitrary object type, which need not be finite; it does
not model infinite individual syntax trees.

Next steps are to obtain region/inclusion evidence from actual declarations and
interpret checked `Core` terms and evaluator values. In particular, `Core.ext`
currently has no initialization argument corresponding to `extendNew`; its
typing rule and evaluation are not certified by these results. Allocation,
lifetimes, mutation, and memory safety require further operational definitions.
