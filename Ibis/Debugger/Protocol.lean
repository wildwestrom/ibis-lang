import Ibis.Debugger.NBT
import Ibis.Topology

namespace Ibis.Debugger
open Spatial Topology

def buildVarInt (n : UInt32) : ByteArray := Id.run do
  let mut n := n
  let mut bytes := ByteArray.empty
  for _ in [:5] do
    if n < 128 then return bytes.push n.toUInt8
    bytes := bytes.push ((n &&& 127).toUInt8 ||| 128)
    n := n >>> 7
  return bytes

def decodeVarInt (bytes : ByteArray) : Except String (UInt32 × ByteArray) := do
  let mut value : UInt32 := 0
  for i in [:5] do
    if i >= bytes.size then throw "truncated VarInt"
    let b := bytes[i]!
    if i == 4 && b > 15 then throw "VarInt exceeds 32 bits"
    value := value ||| ((b &&& 127).toUInt32 <<< (7 * i).toUInt32)
    if b < 128 then return (value, bytes.extract (i + 1) bytes.size)
  throw "VarInt exceeds five bytes"

def mcString (s : String) : ByteArray := buildVarInt s.toUTF8.size.toUInt32 ++ s.toUTF8

def decodeString (bytes : ByteArray) : Except String (ByteArray × ByteArray) := do
  let (len, rest) ← decodeVarInt bytes
  if len.toNat > rest.size then throw "invalid Minecraft string length"
  return (rest.extract 0 len.toNat, rest.extract len.toNat rest.size)

structure Packet where
  id : UInt32
  payload : ByteArray
  deriving BEq

def encodePacket (packet : Packet) : Except String ByteArray := do
  let data := buildVarInt packet.id ++ packet.payload
  if data.size > 2 * 1024 * 1024 then throw "packet too large"
  return buildVarInt data.size.toUInt32 ++ data

def parseHandshake (bytes : ByteArray) : Except String (UInt32 × UInt32) := do
  let (version, rest) ← decodeVarInt bytes
  let (_, rest) ← decodeString rest
  if rest.size < 2 then throw "truncated port"
  let (state, _) ← decodeVarInt (rest.extract 2 rest.size)
  return (version, state)

def readBE (bytes : ByteArray) (offset width : Nat) : Except String Nat := do
  if offset + width > bytes.size then throw "truncated fixed-width value"
  let mut n := 0
  for i in [:width] do n := (n <<< 8) ||| bytes[offset + i]!.toNat
  return n

def parsePosition (bytes : ByteArray) : Except String ChunkPos := do
  let x := Float.ofBits (← readBE bytes 0 8).toUInt64
  let y := Float.ofBits (← readBE bytes 8 8).toUInt64
  let z := Float.ofBits (← readBE bytes 16 8).toUInt64
  if [x, y, z].any (fun f => f.isNaN || f.isInf) then throw "non-finite position"
  let cx := (x / 16).floor
  let cz := (z / 16).floor
  if cx < -2147483648 || cx > 2147483647 || cz < -2147483648 || cz > 2147483647 then
    throw "position exceeds signed chunk coordinates"
  return ⟨cx.toInt64.toUInt64.toUInt32, 0, cz.toInt64.toUInt64.toUInt32⟩

def chunkBuffer (center : ChunkPos) : List ChunkPos :=
  ([-1, 0, 1] : List Int).flatMap fun dx =>
    ([-1, 0, 1] : List Int).map fun dz =>
      ⟨center.x + (UInt32.ofInt dx), 0, center.z + (UInt32.ofInt dz)⟩

def overworldAttributes : NBT := .compound [
  ("piglin_safe", .byte 0), ("natural", .byte 1), ("coordinate_scale", .float 1),
  ("has_skylight", .byte 1), ("has_ceiling", .byte 0), ("ambient_light", .float 0),
  ("infiniburn", .string "minecraft:infiniburn_overworld"), ("has_raids", .byte 1),
  ("logical_height", .int 256), ("respawn_anchor_works", .byte 0),
  ("bed_works", .byte 1), ("ultrawarm", .byte 0)]

def plainsBiome : NBT := .compound [
  ("precipitation", .string "rain"), ("depth", .float 0.125), ("temperature", .float 0.8),
  ("scale", .float 0.05), ("downfall", .float 0.4), ("category", .string "plains"),
  ("effects", .compound [("sky_color", .int 7907327), ("water_fog_color", .int 329011),
    ("fog_color", .int 12638463), ("water_color", .int 4159204)])]

def buildDimensionCodec : Except String ByteArray := buildRootNBT "" (.compound [
  ("minecraft:dimension_type", .compound [
    ("type", .string "minecraft:dimension_type"),
    ("value", .list 10 [.compound [("name", .string "minecraft:overworld"),
      ("id", .int 0), ("element", overworldAttributes)]])]),
  ("minecraft:worldgen/biome", .compound [
    ("type", .string "minecraft:worldgen/biome"),
    ("value", .list 10 [.compound [("name", .string "minecraft:plains"),
      ("id", .int 1), ("element", plainsBiome)]])])])

def buildJoinGame : Except String ByteArray := do
  return be 4 0 ++ ⟨#[0, 1, 255, 1]⟩ ++ mcString "minecraft:overworld" ++
    (← buildDimensionCodec) ++ (← buildRootNBT "" overworldAttributes) ++
    mcString "minecraft:overworld" ++ be 8 0 ++ ⟨#[0, 1, 0, 1, 0, 1]⟩

/-- Upstream's placeholder stone platform; section payloads do not yet affect rendering. -/
def encodeWorldChunk (chunk : WorldChunk Obj c Val) : Except String ByteArray := do
  if chunk.coord.y != 0 then throw "debugger only supports chunks at y=0"
  let height : UInt64 := (List.range 7).foldl (fun n i => n ||| ((64 : UInt64) <<< (i * 9).toUInt64)) 0
  let heights ← buildRootNBT "" (.compound [("MOTION_BLOCKING", .longArray (List.replicate 36 height))])
  let sectionData := be 2 4096 ++ ⟨#[4, 1, 1]⟩ ++ buildVarInt 256 ++ ⟨Array.replicate 2048 0⟩
  return be 4 chunk.coord.x.toNat ++ be 4 chunk.coord.z.toNat ++ ⟨#[1, 8]⟩ ++ heights ++
    buildVarInt 1024 ++ ⟨Array.replicate 1024 1⟩ ++ buildVarInt sectionData.size.toUInt32 ++ sectionData ++ byte 0

end Ibis.Debugger
