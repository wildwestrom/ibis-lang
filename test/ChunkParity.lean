import Ibis.Serialization

open Ibis.Serialization

def main : IO Unit := do
  let chunks : List SerializedChunk := [
    ⟨0, 0, 0, 0, #[], ByteArray.empty⟩,
    ⟨-1, 2, -3, 4, #[0x0102030405060708], ⟨#[0, 255]⟩⟩,
    ⟨-2147483648, 2147483647, 0, -1, #[0, 18446744073709551615, 256], "IBIS".toUTF8⟩]
  for chunk in chunks do
    match (do
      let bytes ← serializeChunk chunk
      let decoded ← deserializeChunk bytes
      if decoded != chunk then throw "chunk round trip failed"
      pure bytes : Except String ByteArray) with
    | .error err => throw (IO.userError err)
    | .ok bytes => IO.println (String.intercalate "," (bytes.data.toList.map (toString ·.toNat)))
