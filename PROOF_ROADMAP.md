# Proof roadmap

Reference: [paper/ibis_semantics.tex](paper/ibis_semantics.tex). This tracks proof
obligations, not a claim that implementing the interpreter in Lean certifies it.

## Completed milestone: region semantics and executable restriction

- [x] Interpret actual `Ibis.Topology.Arrow` and `Section` values in address
  regions, requiring evidence of subset containment for each inclusion.
- [x] Prove `restrictSection` preserves that evidence and commutes with the
  interpretation. Include a rejected inclusion between unrelated regions.
- [x] Generalize binary unique gluing to arbitrary indexed covers, including
  the empty cover of the empty region (paper, “Glueing axiom”).
- [x] State precisely which extension inputs suffice, and why this does not
  yet justify the checker's `Core.ext` rule.
- [x] Implement extension with values only for new addresses; prove preservation
  of old values and initialization of new ones. Prove the existence equivalence.
- [x] Package the union-cover region topology and dependent section sheaf in
  mathlib, with all topology laws and the full covering-sieve sheaf theorem.

Evidence: `IbisProofs/RegionBridge.lean`, `IbisProofs/Regions.lean`, and
`IbisProofs/RegionSheaf.lean`. Scope and assumptions are detailed in [PROOFS.md](PROOFS.md).

## Next milestone: validated site declarations

Trace the elaborated site/cover declarations into runtime objects. Specify the
address-region assignment and the meaning of `Cover u v`, then construct subset
witnesses from accepted declarations. Preserve a rejection case for unrelated
regions. This evidence must be produced by the implementation before the
conditional bridge can certify its uses of restriction.

## Remaining obligations

| Gap | Completion condition | Reference |
| --- | --- | --- |
| Checked language semantics | Define declarative typing and an interpretation of supported `Core`/`Value` terms; prove checker soundness and evaluation preservation, starting with `res`/`ext`. The topology section datatype is not the evaluator's value datatype. | Paper, “The MLTT based type system”; `Ibis/Check.lean`, `Ibis/Eval.lean` |
| Runtime inclusion validation | Obtain subset witnesses from actual site declarations; reject invalid inclusions before execution. Conditional proofs alone do not enforce this. | Paper, “Restriction Maps”; `Ibis/Topology.lean: Arrow.inclusion` |
| Extension semantics | Choose explicit initialization/allocation data or a restricted section model; connect it to typing and evaluation. Prove preservation of old values and initialization of new addresses. | Paper, “Kan Extensions”; `Ibis/Check.lean: infer` |
| Lawful runtime sites | Connect runtime coverage to the now-proved region topology. Raw `SiteTopology.isCover` is only a Boolean predicate. | Paper, “Grothendieck Topology” |
| Runtime gluing | Connect runtime sections and overlap checks to construction of a global section. The specification sheaf is proved; runtime `glue` still only returns a pair. | Paper, “Glueing axiom” |
| Finite materialization | Prove supplied candidates cover the intended region under explicit hypotheses; establish what loading/unloading preserves. Filtering correctness is insufficient. | Paper, “Chunking the topos” |
| Kan constructions | Define the indexing functor/category, colimit identifications and universal property. `Lan`'s existential payload is not this construction. | Paper, “Kan Extensions” |
| Geometric morphisms | Specify the site functor, sheafification and adjunction; prove the required preservation laws. | Paper, “Geometric Morphisms” |
| Memory safety | Define allocation, initialized cells, lifetimes and any mutation/deallocation; state and prove the resulting safety invariant for checked programs. | Paper, Introduction |
| Language metatheory | Formalize substitution, conversion, universes (including the intended impredicative `Prop`), progress/preservation, and inductive positivity/recursors for supported features. | Paper, “The MLTT based type system” |

## Specification corrections to resolve

- Restriction Maps reverses the earlier presheaf convention: an inclusion
  `U ⊆ V` induces `F(V) → F(U)`.
- A morphism alone does not supply a section extension. The region model proves
  both nonuniqueness and possible failure; the failure uses an empty cell type.
- The displayed dependent application rule needs codomain substitution
  `B[x/a]` with an unambiguous binder; the implementation applies a closure.
- Raw arrow syntax is not associative. The existing path interpretation proves
  reassociation preserves restriction, but runtime structural equality remains
  distinct from equality of paths.

The original paper remains unchanged. Record completed results and validation
below; keep the remaining obligations open until their completion conditions hold.

## Validation log

- Initial audit: `lake build IbisProofs`, `lake build`, and all 23 groups in
  `lake exe ibisTests` pass. The 23 existing project theorems and region presheaf
  use only standard Lean axioms; no `sorryAx` or project-specific axioms.
- Region semantics milestone: `lake build IbisProofs` and `lake build` pass
  without warnings; `lake exe ibisTests` passes all 23 groups. Both executable
  extension guards pass. An audit using `#print axioms` on all 34 project
  theorems plus `presheaf`, `regionTopology`, `regionSheaf`, and `extendNew`
  reports only `propext`, `Classical.choice`, and `Quot.sound` where needed;
  `extendNew` itself is axiom-free. No `sorry`, new axioms, or `native_decide`
  were introduced. The README, original paper, and runtime modules are unchanged.
