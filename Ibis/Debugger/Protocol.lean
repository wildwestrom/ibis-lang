import Lean.Data.Json.Printer
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
  -- Clamp the view to the sixteen protocol-754 sections, including below bedrock.
  let cy := (max 0 (min 15 (y / 16).floor)).toUInt32
  return ⟨cx.toInt64.toUInt64.toUInt32, cy, cz.toInt64.toUInt64.toUInt32⟩

def verticalSections (centerY : UInt32) : List UInt32 :=
  (List.range 16).filterMap fun y =>
    if y + 1 >= centerY.toNat && y <= centerY.toNat + 1 then some y.toUInt32 else none

def chunkBuffer (center : ChunkPos) : List ChunkPos :=
  ([-1, 0, 1] : List Int).flatMap fun dx =>
    (verticalSections center.y).flatMap fun y =>
      ([-1, 0, 1] : List Int).map fun dz =>
        ⟨center.x + UInt32.ofInt dx, y, center.z + UInt32.ofInt dz⟩

/-- Unsupported or malformed play payloads are ignored, not interpreted as EOF. -/
inductive PlayPacket where
  | teleportConfirmed : UInt32 → PlayPacket
  | chatReceived : String → PlayPacket
  | position : ChunkPos → PlayPacket
  | clientSettings
  | unknown : Packet → PlayPacket

def decodePlayPacket (packet : Packet) : PlayPacket :=
  let decoded : Except String PlayPacket := do
    match packet.id with
    | 0 => return .teleportConfirmed (← decodeVarInt packet.payload).1
    | 3 =>
      let (bytes, _) ← decodeString packet.payload
      let some text := String.fromUTF8? bytes | throw "invalid UTF-8 chat"
      return .chatReceived text
    | 5 => return .clientSettings
    | 0x11 | 0x12 =>
      let required := if packet.id == 0x11 then 25 else 33
      if packet.payload.size < required then throw "truncated movement"
      return .position (← parsePosition packet.payload)
    | _ => return .unknown packet
  decoded.toOption.getD (.unknown packet)

def packPosition (x y z : Int32) : ByteArray :=
  let bits := ((x.toUInt32.toUInt64 &&& 0x3ffffff) <<< 38) |||
    ((z.toUInt32.toUInt64 &&& 0x3ffffff) <<< 12) ||| (y.toUInt32.toUInt64 &&& 0xfff)
  be 8 bits.toNat

def systemChatMessage (text : String) : ByteArray :=
  mcString (Lean.Json.mkObj [("text", .str text)]).compress ++ byte 1 ++ ⟨Array.replicate 16 0⟩

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
    mcString "minecraft:overworld" ++ be 8 0 ++ ⟨#[1, 1, 1, 1, 0, 1]⟩

/-- Upstream's placeholder stone platform; section payloads do not yet affect rendering. -/
def encodeWorldChunk (chunk : WorldChunk Obj c Val) : Except String ByteArray := do
  if chunk.coord.y > 15 then throw "debugger section must be between 0 and 15"
  let top := (chunk.coord.y.toUInt64 + 1) * 16
  let height : UInt64 := (List.range 7).foldl (fun n i => n ||| (top <<< (i * 9).toUInt64)) 0
  let heights ← buildRootNBT "" (.compound [("MOTION_BLOCKING", .longArray (List.replicate 36 height))])
  let sectionData := be 2 4096 ++ ⟨#[4, 1, 1]⟩ ++ buildVarInt 256 ++ ⟨Array.replicate 2048 0⟩
  return be 4 chunk.coord.x.toNat ++ be 4 chunk.coord.z.toNat ++ byte 1 ++ buildVarInt ((1 : UInt32) <<< chunk.coord.y) ++ heights ++
    buildVarInt 1024 ++ ⟨Array.replicate 1024 1⟩ ++ buildVarInt sectionData.size.toUInt32 ++ sectionData ++ byte 0

end Ibis.Debugger
