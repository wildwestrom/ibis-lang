import Std

namespace Ibis.Serialization

/-- Upstream's wire record. Signed coordinates are independent of spatial `ChunkPos`. -/
structure SerializedChunk where
  x : Int32
  y : Int32
  z : Int32
  depth : Int32
  arrowIds : Array UInt64
  payload : ByteArray
  deriving BEq

def chunkMagicNumber : ByteArray := "IBIS".toUTF8

private def putLE (bytes : ByteArray) (width value : Nat) : ByteArray := Id.run do
  let mut bytes := bytes
  for i in [:width] do
    bytes := bytes.push ((value >>> (8 * i)).toUInt8)
  return bytes

/-- Reject unrepresentable lengths instead of silently truncating the wire headers. -/
def serializeChunk (chunk : SerializedChunk) : Except String ByteArray := do
  if chunk.arrowIds.size >= 2^32 || chunk.payload.size >= 2^32 then
    throw "chunk length exceeds the 32-bit wire format"
  let mut bytes := chunkMagicNumber
  for value in [chunk.x, chunk.y, chunk.z, chunk.depth] do
    bytes := putLE bytes 4 value.toUInt32.toNat
  bytes := putLE bytes 4 chunk.arrowIds.size
  for arrow in chunk.arrowIds do
    bytes := putLE bytes 8 arrow.toNat
  return (putLE bytes 4 chunk.payload.size) ++ chunk.payload

private def getLE (bytes : ByteArray) (offset width : Nat) : Except String Nat := do
  if offset + width > bytes.size then throw "truncated chunk"
  let mut value := 0
  for i in [:width] do
    value := value ||| (bytes[offset + i]!.toNat <<< (8 * i))
  return value

/-- Like upstream, reads one chunk and ignores trailing bytes. Counts are checked
    against the input size before allocating or iterating over them. -/
def deserializeChunk (bytes : ByteArray) : Except String SerializedChunk := do
  if bytes.extract 0 4 != chunkMagicNumber then throw "invalid chunk magic number"
  let x := (← getLE bytes 4 4).toUInt32.toInt32
  let y := (← getLE bytes 8 4).toUInt32.toInt32
  let z := (← getLE bytes 12 4).toUInt32.toInt32
  let depth := (← getLE bytes 16 4).toUInt32.toInt32
  let count ← getLE bytes 20 4
  let payloadOffset := 24 + count * 8 + 4
  if payloadOffset > bytes.size then throw "truncated chunk arrow array"
  let mut arrowIds := #[]
  for i in [:count] do
    arrowIds := arrowIds.push (← getLE bytes (24 + i * 8) 8).toUInt64
  let payloadLength ← getLE bytes (payloadOffset - 4) 4
  if payloadOffset + payloadLength > bytes.size then throw "truncated chunk payload"
  return ⟨x, y, z, depth, arrowIds, bytes.extract payloadOffset (payloadOffset + payloadLength)⟩

end Ibis.Serialization
