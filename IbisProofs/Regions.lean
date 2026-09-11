import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Lattice

/-! A specification model motivated by `paper/ibis_semantics.tex`.
Regions are sets of addresses (equivalently opens for the discrete topology).
Sections assign a value of the address's cell type at every address in a region.
This is not yet an interpretation of Ibis terms or a model of allocation. -/

namespace Ibis.Regions

open CategoryTheory Opposite

variable {Addr : Type} {Cell : Addr → Type}

abbrev Region (Addr : Type) := Set Addr
abbrev Section (Cell : Addr → Type) (U : Region Addr) := ∀ a : U, Cell a.val

/-- Only a genuine subset inclusion authorizes restriction. -/
def restrict {U V : Region Addr} (h : U ⊆ V) (s : Section Cell V) : Section Cell U :=
  fun a => s ⟨a.val, h a.property⟩

@[simp] theorem restrict_id {U : Region Addr} (s : Section Cell U) :
    restrict (Set.Subset.refl U) s = s := rfl

theorem restrict_comp {U V W : Region Addr} (h : U ⊆ V) (k : V ⊆ W)
    (s : Section Cell W) : restrict h (restrict k s) = restrict (h.trans k) s := rfl

/-- A presheaf in mathlib's sense, with all functor laws proved. -/
def presheaf (Cell : Addr → Type) : (Region Addr)ᵒᵖ ⥤ Type where
  obj U := Section Cell U.unop
  map f := TypeCat.ofHom (restrict (leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

def Compatible {U V : Region Addr} (s : Section Cell U) (t : Section Cell V) : Prop :=
  ∀ (a : Addr) (hu : a ∈ U) (hv : a ∈ V), s ⟨a, hu⟩ = t ⟨a, hv⟩

/-- Agreement on the overlap gives exactly one section on the union. -/
theorem existsUnique_glue {U V : Region Addr} (s : Section Cell U)
    (t : Section Cell V) (agree : Compatible s t) :
    ∃! g : Section Cell (U ∪ V),
      restrict Set.subset_union_left g = s ∧ restrict Set.subset_union_right g = t := by
  classical
  let g : Section Cell (U ∪ V) := fun a =>
    if hu : a.val ∈ U then s ⟨a.val, hu⟩ else t ⟨a.val, a.property.resolve_left hu⟩
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · funext a
    simp [restrict, g, a.property]
  · funext a
    dsimp [restrict, g]
    split
    · exact agree a.val _ a.property
    · rfl
  · intro other h
    funext a
    rcases a with ⟨a, ha⟩
    by_cases hu : a ∈ U
    · have eq := congrFun h.1 ⟨a, hu⟩
      simpa [restrict, g, hu] using eq
    · have eq := congrFun h.2 ⟨a, ha.resolve_left hu⟩
      simpa [restrict, g, hu] using eq

/-- Supplying values on the larger region makes extension possible. This is an
explicit extra input, not an operation supplied by the presheaf laws. -/
noncomputable def extendWith {U V : Region Addr} (_h : U ⊆ V)
    (s : Section Cell U) (fill : Section Cell V) : Section Cell V := by
  classical
  exact fun a => if hu : a.val ∈ U then s ⟨a.val, hu⟩ else fill a

theorem restrict_extendWith {U V : Region Addr} (h : U ⊆ V)
    (s : Section Cell U) (fill : Section Cell V) :
    restrict h (extendWith h s fill) = s := by
  classical
  funext a
  simp [restrict, extendWith, a.property]

/-- Extending one local section is different from gluing compatible sections.
On a newly added address, two distinct values give two distinct extensions. -/
theorem extension_not_unique :
    ∃ s : Section (fun _ : Bool => Bool) {false},
      ∃ g₁ g₂ : Section (fun _ : Bool => Bool) Set.univ,
        restrict (Set.subset_univ _) g₁ = s ∧
        restrict (Set.subset_univ _) g₂ = s ∧ g₁ ≠ g₂ := by
  refine ⟨fun _ => false, fun _ => false, fun a => a.val, rfl, ?_, ?_⟩
  · funext a
    exact a.property
  · intro h
    have impossible := congrFun h ⟨true, Set.mem_univ _⟩
    cases impossible

/-- A legitimate dependent cell family with no available value at address `true`. -/
def PartialCell : Bool → Type
  | false => Unit
  | true => Empty

/-- Even a lawful presheaf need not let a local section extend to a larger region. -/
theorem extension_can_fail :
    Nonempty (Section PartialCell {false}) ∧
      ¬ Nonempty (Section PartialCell (Set.univ : Region Bool)) := by
  constructor
  · refine ⟨fun a => ?_⟩
    have h : a.val = false := a.property
    rw [h]
    exact ()
  · rintro ⟨s⟩
    exact (s ⟨true, Set.mem_univ _⟩).elim

end Ibis.Regions
