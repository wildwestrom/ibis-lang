import Ibis.Topology

/-! Proofs about the executable topology prototype. These do not assume that its
raw arrows form a category or that overlap agreement supplies a global section. -/

namespace Ibis.Topology

variable {Obj Val : Type} {u v w x : Obj}

@[simp] theorem Arrow.compose_id (f : Arrow Obj u v) : f.compose .id = f := by
  cases f <;> rfl

@[simp] theorem Arrow.id_compose (f : Arrow Obj u v) : Arrow.id.compose f = f := by
  cases f <;> rfl

/-- The smart composition operation has the same restriction semantics as `comp`. -/
theorem restrictSection_compose (g : Arrow Obj v w) (f : Arrow Obj u v)
    (s : Section Val w) :
    restrictSection (g.compose f) s = restrictSection f (restrictSection g s) := by
  cases g <;> cases f <;> rfl

/-- Reassociation changes raw syntax, but cannot change its action on sections. -/
theorem restrictSection_assoc (h : Arrow Obj w x) (g : Arrow Obj v w)
    (f : Arrow Obj u v) (s : Section Val x) :
    restrictSection ((h.compose g).compose f) s =
      restrictSection (h.compose (g.compose f)) s := by
  simp only [restrictSection_compose]

/-- Three inclusions witness the failure of associativity for raw syntax. -/
theorem Arrow.compose_not_associative (p : Ibis.Spatial.LocalPos) :
    let a : Arrow Unit () () := .inclusion p
    (a.compose a).compose a ≠ a.compose (a.compose a) := by
  dsimp [Arrow.compose]
  intro h
  have impossible := congrArg (fun t : Arrow Unit () () =>
    match t with
    | .comp (.comp _ _) _ => true
    | _ => false) h
  cases impossible

theorem maximalSieve_closed : (maximalSieve (Obj := Obj) (c := u)).closed := by
  intro _ _ _ _ _
  rfl

@[simp] theorem pullbackSieve_id (s : Sieve Obj u) : pullbackSieve .id s = s := by
  cases s
  simp [pullbackSieve]

/-- Filtering keeps exactly the supplied candidates accepted by the sieve.
This does not claim that the finite list exhausts an infinite sieve or covers. -/
theorem mem_materializeSieve (depth : Int) (candidates : List (CoveringArrow Obj u))
    (s : Sieve Obj u) (a : CoveringArrow Obj u) :
    a ∈ (materializeSieve depth candidates s).arrows ↔
      a ∈ candidates ∧ s.contains a.arrow = true := by
  simp [materializeSieve]

/-- Boolean agreement certifies equality only when the equality test is lawful. -/
theorem glue_eq_some_iff (p : Presheaf Obj) [BEq (p.fiber w)]
    [LawfulBEq (p.fiber w)] (a : Arrow Obj w u) (b : Arrow Obj w v)
    (s : p.fiber u) (t : p.fiber v) :
    glue p a b s t = some ⟨s, t⟩ ↔ p.restrict a s = p.restrict b t := by
  simp [glue]

/-- Successful generation certifies the predicate and the precise filtered payload;
it does not turn the supplied site predicate into a lawful topology. -/
theorem generateChunk_eq_ok_iff (site : GrothendieckSite Obj)
    (coord : Ibis.Spatial.ChunkPos) (payload : Section Val u)
    (candidates : List (CoveringArrow Obj u)) (s : Sieve Obj u)
    (chunk : WorldChunk Obj u Val) :
    generateChunk site coord payload candidates s = .ok chunk ↔
      isCoveringSieve site s = true ∧
        chunk = ⟨coord, materializeSieve (Int.ofNat coord.y.toNat) candidates s, payload⟩ := by
  cases h : isCoveringSieve site s <;> simp [generateChunk, h, eq_comm]

end Ibis.Topology
