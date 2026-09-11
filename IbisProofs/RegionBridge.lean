import IbisProofs.Regions
import IbisProofs.Topology

/-! A conditional interpretation of the executable topology datatype, not of
`Core` or `Value`. Every inclusion needs actual subset evidence. Empty runtime
sections denote absent values; base sections denote constant present values.
No allocation or initialization is inferred from absence. -/

namespace Ibis.Regions.Runtime

variable {Obj Addr Val : Type} (region : Obj → Region Addr)

/-- Validate every edge, including intermediate regions of a composition. -/
def ValidArrow : {u v : Obj} → Topology.Arrow Obj u v → Prop
  | _, _, .id => True
  | u, v, .inclusion _ => region u ⊆ region v
  | _, _, .comp g f => ValidArrow g ∧ ValidArrow f

theorem ValidArrow.subset {u v : Obj} (a : Topology.Arrow Obj u v)
    (ha : ValidArrow region a) : region u ⊆ region v := by
  induction a with
  | id => exact Set.Subset.refl _
  | inclusion _ => exact ha
  | comp g f ihg ihf => exact (ihf ha.2).trans (ihg ha.1)

/-- Sections are interpretable only if all their stored restrictions are valid. -/
def ValidSection : {u : Obj} → Topology.Section Val u → Prop
  | _, .empty => True
  | _, .base _ => True
  | _, .restrict a s => ValidArrow region a ∧ ValidSection s

/-- Interpret the actual runtime syntax as an optional value at each address.
`none` records an empty payload; it does not certify an initialized memory cell. -/
def interpret : {u : Obj} → (s : Topology.Section Val u) →
    ValidSection region s → Section (fun _ => Option Val) (region u)
  | _, .empty, _ => fun _ => none
  | _, .base v, _ => fun _ => some v
  | _, .restrict a s, hs =>
    restrict (ValidArrow.subset region a hs.1) (interpret s hs.2)

theorem valid_restrictSection {u v : Obj} (a : Topology.Arrow Obj u v)
    (ha : ValidArrow region a) (s : Topology.Section Val v)
    (hs : ValidSection region s) : ValidSection region (Topology.restrictSection a s) := by
  induction a with
  | id => exact hs
  | inclusion _ => exact ⟨ha, hs⟩
  | comp g f ihg ihf => exact ihf ha.2 _ (ihg ha.1 s hs)

/-- The executable restriction function commutes with address-level restriction. -/
theorem interpret_restrictSection {u v : Obj} (a : Topology.Arrow Obj u v)
    (ha : ValidArrow region a) (s : Topology.Section Val v)
    (hs : ValidSection region s) :
    interpret region (Topology.restrictSection a s)
        (valid_restrictSection region a ha s hs) =
      restrict (ValidArrow.subset region a ha) (interpret region s hs) := by
  induction a with
  | id => rfl
  | inclusion _ => rfl
  | comp g f ihg ihf =>
    change interpret region (Topology.restrictSection f (Topology.restrictSection g s)) _ = _
    rw [ihf ha.2 _ (valid_restrictSection region g ha.1 s hs), ihg ha.1 s hs]
    rfl

/-- An inclusion constructor alone cannot certify unrelated singleton regions. -/
theorem unrelated_inclusion_invalid (p : Ibis.Spatial.LocalPos) :
    ¬ ValidArrow (fun b : Bool => ({b} : Region Bool))
      (.inclusion p : Topology.Arrow Bool false true) := by
  intro h
  have bad : false ∈ ({true} : Region Bool) := h (Set.mem_singleton false)
  cases bad

end Ibis.Regions.Runtime
