import Std

namespace Ibis.Debugger

def be (width value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [:width] do bytes := bytes.push ((value >>> (8 * (width - 1 - i))).toUInt8)
  return bytes

def byte (value : UInt8) : ByteArray := ⟨#[value]⟩

def concat (parts : List ByteArray) : ByteArray := parts.foldl (· ++ ·) ByteArray.empty

inductive NBT where
  | byte : UInt8 → NBT
  | int : Int32 → NBT
  | float : Float32 → NBT
  | string : String → NBT
  | list : UInt8 → List NBT → NBT
  | compound : List (String × NBT) → NBT
  | longArray : List UInt64 → NBT

def NBT.tagId : NBT → UInt8
  | .byte _ => 1 | .int _ => 3 | .float _ => 5 | .string _ => 8
  | .list .. => 9 | .compound _ => 10 | .longArray _ => 12

def nbtString (s : String) : Except String ByteArray := do
  let bytes := s.toUTF8
  if bytes.size > 65535 then throw "NBT string exceeds 65535 bytes"
  return be 2 bytes.size ++ bytes

partial def NBT.encodeValue : NBT → Except String ByteArray
  | .byte n => pure (Debugger.byte n)
  | .int n => pure (be 4 n.toUInt32.toNat)
  | .float n => pure (be 4 n.toBits.toNat)
  | .string s => nbtString s
  | .list tag xs => do
    if xs.length >= 2^31 then throw "NBT list too long"
    if xs.any (·.tagId != tag) then throw "NBT list tag mismatch"
    return Debugger.byte tag ++ be 4 xs.length ++ concat (← xs.mapM NBT.encodeValue)
  | .compound fields => do
    let parts ← fields.mapM fun (name, val) => do
      return Debugger.byte val.tagId ++ (← nbtString name) ++ (← val.encodeValue)
    return concat parts ++ Debugger.byte 0
  | .longArray xs => do
    if xs.length >= 2^31 then throw "NBT array too long"
    return be 4 xs.length ++ concat (xs.map (fun n => be 8 n.toNat))

def buildRootNBT (name : String) (tag : NBT) : Except String ByteArray := do
  return byte tag.tagId ++ (← nbtString name) ++ (← tag.encodeValue)

end Ibis.Debugger
