import IbisProofs.Regions
import Mathlib.CategoryTheory.Sites.Sheaf

/-! The address-region model as a mathlib site and sheaf. All subsets are regions,
so singletons form a cover basis. This does not certify runtime site predicates. -/

namespace Ibis.Regions

open CategoryTheory Opposite

variable {Addr : Type}

/-- The union-cover topology on sets of addresses, expressed using the singleton
basis. Downward closure makes this equivalent to the usual pointwise coverage. -/
def regionTopology (Addr : Type) : GrothendieckTopology (Region Addr) where
  sieves U := {S | ∀ (a : Addr) (ha : a ∈ U),
    S (homOfLE (Set.singleton_subset_iff.mpr ha))}
  top_mem' _ := fun _ _ => trivial
  pullback_stable' := by
    intro U V S f hS a ha
    exact hS a (leOfHom f ha)
  transitive' := by
    intro U S hS R hR a ha
    exact hR (hS a ha) a (Set.mem_singleton a)

/-- Covering means that every address belongs to a region in the sieve. -/
theorem mem_regionTopology_iff {U : Region Addr} (S : CategoryTheory.Sieve U) :
    S ∈ regionTopology Addr U ↔
      ∀ a ∈ U, ∃ (V : Region Addr) (f : V ⟶ U), S f ∧ a ∈ V := by
  constructor
  · intro h a ha
    exact ⟨{a}, homOfLE (Set.singleton_subset_iff.mpr ha), h a ha,
      Set.mem_singleton a⟩
  · intro h a ha
    obtain ⟨V, f, hf, hav⟩ := h a ha
    exact S.downward_closed hf (homOfLE (Set.singleton_subset_iff.mpr hav))

/-- Empty coverage is valid exactly for the empty region. -/
theorem empty_sieve_covers_iff (U : Region Addr) :
    (⊥ : CategoryTheory.Sieve U) ∈ regionTopology Addr U ↔ U = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact h a ha
  · rintro rfl a ha
    exact ha.elim

/-- Dependent address-valued sections satisfy the full mathlib sheaf condition,
including the empty region and arbitrary covering sieves. -/
theorem presheaf_isSheaf (Cell : Addr → Type) :
    CategoryTheory.Presheaf.IsSheaf (regionTopology Addr) (presheaf Cell) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  intro U S hS s agree
  let point (a : U) : ({a.val} : Region Addr) ⟶ U :=
    homOfLE (Set.singleton_subset_iff.mpr a.property)
  let g : Section Cell U := fun a => s (point a) (hS a.val a.property)
    ⟨a.val, Set.mem_singleton a.val⟩
  refine ⟨g, ?_, ?_⟩
  · intro V f hf
    funext a
    let b : U := ⟨a.val, leOfHom f a.property⟩
    have eq := agree (𝟙 ({a.val} : Region Addr))
      (homOfLE (Set.singleton_subset_iff.mpr a.property))
      (hS b.val b.property) hf (Subsingleton.elim _ _)
    exact congrFun eq ⟨a.val, Set.mem_singleton a.val⟩
  · intro other h
    funext a
    exact congrFun (h (point a) (hS a.val a.property))
      ⟨a.val, Set.mem_singleton a.val⟩

/-- The specification model packaged as a mathlib sheaf. -/
def regionSheaf (Cell : Addr → Type) :
    CategoryTheory.Sheaf (regionTopology Addr) (Type) :=
  ⟨presheaf Cell, presheaf_isSheaf Cell⟩

end Ibis.Regions
