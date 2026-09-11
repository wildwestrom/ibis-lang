import IbisProofs.Topology
import Mathlib.CategoryTheory.PathCategory.Basic

/-! A mathematical interpretation of raw Ibis arrows in mathlib's free path
category. No extra geometric equations are imposed, and the runtime is unchanged. -/

namespace Ibis.Topology

/-- A wrapper keeps the inclusion quiver local to this model. -/
structure PathObject (Obj : Type) where
  index : Obj

instance : Quiver (PathObject Obj) where
  Hom _ _ := Ibis.Spatial.LocalPos

/-- Mathlib supplies identity and associative composition for paths of inclusions. -/
abbrev InclusionCategory (Obj : Type) := CategoryTheory.Paths (PathObject Obj)

variable {Obj Val : Type} {u v w x : Obj}

/-- Forget composition-tree parentheses, retaining each inclusion and its endpoints. -/
def Arrow.toPath : {u v : Obj} → Arrow Obj u v →
    Quiver.Path (PathObject.mk u) (PathObject.mk v)
  | _, _, .id => .nil
  | _, _, .inclusion p => .cons .nil p
  | _, _, .comp g f => f.toPath.comp g.toPath

@[simp] theorem Arrow.toPath_compose (g : Arrow Obj v w) (f : Arrow Obj u v) :
    (g.compose f).toPath = f.toPath.comp g.toPath := by
  cases g <;> cases f <;> simp [Arrow.compose, Arrow.toPath]

/-- Unlike the raw syntax, the path interpretation obeys associativity. -/
theorem Arrow.toPath_assoc (h : Arrow Obj w x) (g : Arrow Obj v w)
    (f : Arrow Obj u v) :
    ((h.compose g).compose f).toPath = (h.compose (g.compose f)).toPath := by
  simp only [Arrow.toPath_compose, Quiver.Path.comp_assoc]

/-- Interpret a path contravariantly on the prototype's actual sections. -/
def restrictPath {u v : PathObject Obj} (p : Quiver.Path u v)
    (s : Section Val v.index) : Section Val u.index :=
  match p with
  | .nil => s
  | .cons q e => restrictPath q (.restrict (.inclusion e) s)

theorem restrictPath_comp {u v w : PathObject Obj}
    (p : Quiver.Path u v) (q : Quiver.Path v w) (s : Section Val w.index) :
    restrictPath (p.comp q) s = restrictPath p (restrictPath q s) := by
  induction q with
  | nil => rfl
  | cons q e ih => exact ih (.restrict (.inclusion e) s)

/-- The path interpretation preserves the existing executable restriction semantics. -/
theorem restrictPath_toPath (a : Arrow Obj u v) (s : Section Val v) :
    restrictPath a.toPath s = restrictSection a s := by
  induction a with
  | id => rfl
  | inclusion p => rfl
  | comp g f ihg ihf =>
    simp only [Arrow.toPath, restrictPath_comp, ihg, ihf, restrictSection]

/-- Equal paths are interchangeable when restricting any section. -/
theorem restrictSection_eq_of_toPath_eq (a b : Arrow Obj u v)
    (h : a.toPath = b.toPath) (s : Section Val v) :
    restrictSection a s = restrictSection b s := by
  rw [← restrictPath_toPath, ← restrictPath_toPath, h]

end Ibis.Topology
