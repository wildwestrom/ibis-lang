import Ibis.Spatial

namespace Ibis.Topology

open Ibis.Spatial

/-- The prototype's indexed syntax of identity, inclusion, and composition arrows. -/
inductive Arrow (Obj : Type) : Obj → Obj → Type where
  | id : Arrow Obj u u
  | inclusion : LocalPos → Arrow Obj u v
  | comp : Arrow Obj v w → Arrow Obj u v → Arrow Obj u w

def Arrow.compose (g : Arrow Obj v w) (f : Arrow Obj u v) : Arrow Obj u w :=
  match g, f with
  | .id, f => f
  | g, .id => g
  | g, f => .comp g f

abbrev OpArrow (Obj : Type) (u v : Obj) := Arrow Obj v u

def composeOp (g : OpArrow Obj v w) (f : OpArrow Obj u v) : OpArrow Obj u w :=
  Arrow.compose f g

structure Sieve (Obj : Type) (c : Obj) where
  contains : {d : Obj} → Arrow Obj d c → Bool

def maximalSieve : Sieve Obj c := ⟨fun _ => true⟩

def pullbackSieve (g : Arrow Obj d c) (s : Sieve Obj c) : Sieve Obj d :=
  ⟨fun h => s.contains (g.compose h)⟩

structure SiteTopology (Obj : Type) where
  isCover : {c : Obj} → Sieve Obj c → Bool

structure GrothendieckSite (Obj : Type) where
  topology : SiteTopology Obj

def isCoveringSieve (site : GrothendieckSite Obj) (s : Sieve Obj c) : Bool :=
  site.topology.isCover s

/-- Laws are explicit proof obligations, separate from the executable prototype's predicates.
    Raw `Sieve` and `SiteTopology` values do not imply these laws. -/
def Sieve.closed (s : Sieve Obj c) : Prop :=
  ∀ {d e} (f : Arrow Obj d c) (g : Arrow Obj e d), s.contains f = true → s.contains (f.compose g) = true

structure TopologyLaws (j : SiteTopology Obj) : Prop where
  maximal : ∀ c, j.isCover (maximalSieve (c := c)) = true
  stable : ∀ {c d} (s : Sieve Obj c) (g : Arrow Obj d c),
    j.isCover s = true → j.isCover (pullbackSieve g s) = true
  localCharacter : ∀ {c} (s r : Sieve Obj c), j.isCover s = true →
    (∀ {d} (f : Arrow Obj d c), s.contains f = true → j.isCover (pullbackSieve f r) = true) →
    j.isCover r = true

theorem pullback_maximal (g : Arrow Obj d c) :
    pullbackSieve g maximalSieve = maximalSieve := rfl

inductive Section (Val : Type) {Obj : Type} : Obj → Type where
  | empty : Section Val u
  | base : Val → Section Val u
  | restrict : Arrow Obj u v → Section Val v → Section Val u

def restrictSection (a : Arrow Obj u v) (s : Section Val v) : Section Val u :=
  match a with
  | .id => s
  | .inclusion pos => .restrict (.inclusion pos) s
  | .comp g f => restrictSection f (restrictSection g s)

structure Presheaf (Obj : Type) where
  fiber : Obj → Type
  restrict : {u v : Obj} → Arrow Obj u v → fiber v → fiber u

structure PresheafLaws (p : Presheaf Obj) : Prop where
  identity : ∀ {u} (s : p.fiber u), p.restrict .id s = s
  composition : ∀ {u v w} (f : Arrow Obj u v) (g : Arrow Obj v w) (s : p.fiber w),
    p.restrict (.comp g f) s = p.restrict f (p.restrict g s)

def sectionPresheaf (Obj Val : Type) : Presheaf Obj :=
  ⟨Section Val, restrictSection⟩

theorem sectionPresheaf_laws : PresheafLaws (sectionPresheaf Obj Val) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

def pullback (p : Presheaf Obj) (a : Arrow Obj u v) (s : p.fiber v) : p.fiber u :=
  p.restrict a s

/-- The existential payload of a left Kan extension. A presheaf alone cannot
    extend sections covariantly; this remains a container until an extension map is supplied. -/
structure Lan (p : Presheaf Obj) (u : Obj) where
  source : Obj
  arrow : Arrow Obj source u
  payload : p.fiber source

def Lan.map (a : Arrow Obj u v) (s : Lan p u) : Lan p v :=
  ⟨s.source, a.compose s.arrow, s.payload⟩

structure GluedSection (p : Presheaf Obj) (u v : Obj) where
  left : p.fiber u
  right : p.fiber v

/-- Checks agreement on the given overlap; it does not construct a global amalgamation. -/
def glue (p : Presheaf Obj) [BEq (p.fiber w)] (a : Arrow Obj w u) (b : Arrow Obj w v)
    (x : p.fiber u) (y : p.fiber v) : Option (GluedSection p u v) :=
  if p.restrict a x == p.restrict b y then some ⟨x, y⟩ else none

structure CoveringArrow (Obj : Type) (c : Obj) where
  source : Obj
  arrow : Arrow Obj source c

structure FiniteCover (Obj : Type) (c : Obj) where
  depth : Int
  arrows : List (CoveringArrow Obj c)

abbrev SectorCoord := Int × Int × Int

structure WorldChunk (Obj : Type) (c : Obj) (Val : Type) where
  coord : ChunkPos
  coverage : FiniteCover Obj c
  payload : Section Val c

/-- Compatibility name for the previous chunk type. -/
abbrev VoxelChunk := WorldChunk

structure Region (Obj : Type) (c : Obj) (Val : Type) where
  chunks : List (WorldChunk Obj c Val)
  chunkCount : Nat

structure World (Obj : Type) (c : Obj) (Val : Type) where
  site : GrothendieckSite Obj
  chunks : List (WorldChunk Obj c Val)

def materializeSieve (depth : Int) (candidates : List (CoveringArrow Obj c)) (s : Sieve Obj c) :
    FiniteCover Obj c :=
  ⟨depth, candidates.filter fun a => s.contains a.arrow⟩

def generateChunk (site : GrothendieckSite Obj) (coord : ChunkPos) (payload : Section Val c)
    (candidates : List (CoveringArrow Obj c)) (sieve : Sieve Obj c) : Except String (WorldChunk Obj c Val) :=
  if isCoveringSieve site sieve then
    .ok ⟨coord, materializeSieve (Int.ofNat coord.y.toNat) candidates sieve, payload⟩
  else .error "sieve does not cover the chunk's spatial index object"

def localRestriction (pos : LocalPos) : Arrow Obj target c := .inclusion pos

def localComposition (middle : Obj) (pos₁ pos₂ : LocalPos) : Arrow Obj target c :=
  .comp (.inclusion (u := middle) pos₂) (.inclusion pos₁)

/-- Compare arrow syntax without deriving any equality of object indices. -/
def Arrow.samePath (a : Arrow Obj u v) (b : Arrow Obj u' v') : Bool :=
  match a, b with
  | .id, .id => true
  | .inclusion p, .inclusion q => p == q
  | .comp g f, .comp g' f' => g.samePath g' && f.samePath f'
  | _, _ => false

/-- Unlike upstream's unsafe cast, target equality must be checked independently. -/
def eqArrow [DecidableEq Obj] (a : Arrow Obj u v) (b : Arrow Obj u w) : Option (PLift (v = w)) :=
  if h : v = w then if a.samePath b then some ⟨h⟩ else none else none

def chunkAt (world : World Obj c Val) (coord : ChunkPos) : Option (WorldChunk Obj c Val) :=
  world.chunks.find? fun chunk => chunk.coord == coord

def sectionIn (world : World Obj c Val) (coord : ChunkPos) (arrow : Arrow Obj target c) :
    Option (Section Val target) :=
  (chunkAt world coord).map fun chunk => .restrict arrow chunk.payload

/-- Zero in any dimension produces an empty world; dimensions never wrap on subtraction. -/
def generateWorld (site : GrothendieckSite Obj) (size : UInt32 × UInt32 × UInt32) :
    Except String (World Obj c Val) := do
  let (width, height, depth) := size
  if width == 0 || height == 0 || depth == 0 then return ⟨site, []⟩
  let mut chunks := []
  for x in [:width.toNat] do
    for y in [:height.toNat] do
      for z in [:depth.toNat] do
        let chunk ← generateChunk site ⟨x.toUInt32, y.toUInt32, z.toUInt32⟩
          (.empty : Section Val c) [] maximalSieve
        chunks := chunk :: chunks
  return ⟨site, chunks.reverse⟩

end Ibis.Topology
