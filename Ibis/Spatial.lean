import Ibis.Syntax

namespace Ibis.Spatial

structure ChunkPos where
  x : UInt32
  y : UInt32
  z : UInt32
  deriving Repr, BEq, Inhabited

structure LocalCoord where
  x : UInt8
  y : UInt8
  z : UInt8
  deriving Repr, BEq, Inhabited

structure Coord where
  chunk : ChunkPos
  localCoord : LocalCoord
  deriving Repr, BEq, Inhabited

/-- Spatial syntax stores child addresses; no disk streaming is implied by these types. -/
inductive CoTerm where
  | universe : Nat → CoTerm
  | const : String → CoTerm
  | mvar : Nat → CoTerm
  | var : Nat → CoTerm
  | lit : Literal → CoTerm
  | unit
  | pi : Option String → Coord → Coord → CoTerm
  | lam : Option String → Coord → CoTerm
  | app : Coord → Coord → CoTerm
  | sigma : Option String → Coord → Coord → CoTerm
  | pair : Coord → Coord → CoTerm
  | fst : Coord → CoTerm
  | snd : Coord → CoTerm
  | letE : Coord → Coord → CoTerm
  | ann : Coord → Coord → CoTerm
  | matchE : Coord → List (Pat × Coord) → CoTerm
  | site : Nat → CoTerm
  | cover : Coord → Coord → CoTerm
  | sect : Coord → Coord → CoTerm
  | res : Coord → Coord → Coord → Coord → Coord → CoTerm
  | ext : Coord → Coord → Coord → Coord → Coord → CoTerm
  deriving Repr, BEq

inductive CoDecl where
  | defn : String → CoTerm → CoTerm → CoDecl
  | inductiveE : String → CoTerm → List (String × CoTerm) → CoDecl
  deriving Repr, BEq

mutual
  inductive Value where
    | universe : Nat → Value
    | const : String → Value
    | lit : Literal → Value
    | pair : Value → Value → Value
    | pi : Option String → Value → Closure → Value
    | lam : Option String → Value → Closure → Value
    | sigma : Option String → Value → Closure → Value
    | site : Nat → Value
    | cover : Value → Value → Value
    | sect : Value → Value → Value
    | neutral : Value → Neutral → Value
    deriving Repr, BEq
  inductive Neutral where
    | var : Nat → Neutral
    | app : Neutral → Value → Neutral
    | fst : Neutral → Neutral
    | snd : Neutral → Neutral
    | matchE : Neutral → List (Pat × Value) → Neutral
    | res : Value → Value → Value → Value → Neutral → Neutral
    | ext : Value → Value → Value → Value → Neutral → Neutral
    deriving Repr, BEq
  inductive Closure where
    | mk : List Value → Coord → Closure
    deriving Repr, BEq
end

structure CoChunk where
  position : ChunkPos
  locals : List LocalCoord
  deriving Repr, BEq

structure CoWorld where
  chunks : List (ChunkPos × CoChunk)
  origin : ChunkPos
  deriving Repr, BEq

end Ibis.Spatial

namespace Ibis.CFG

inductive Terminator (E : Type) where
  | goto : Nat → Terminator E
  | branch : E → Nat → Nat → Terminator E
  | ret : Option E → Terminator E
  | unreachable
  deriving Repr, BEq

inductive Instruction (T E : Type) where
  | declare : String → T → Instruction T E
  | assign : String → E → Instruction T E
  | store : E → E → Instruction T E
  | call : Option String → E → List E → Instruction T E
  | comment : String → Instruction T E
  deriving Repr, BEq

structure BasicBlock (T E : Type) where
  id : Nat
  instructions : List (Instruction T E)
  terminator : Terminator E
  deriving Repr, BEq

structure Graph (T E : Type) where
  entry : Nat
  blocks : List (BasicBlock T E)
  deriving Repr, BEq

end Ibis.CFG
