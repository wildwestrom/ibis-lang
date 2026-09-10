import Ibis.Debugger.NBT
open Ibis.Debugger

def main : IO Unit := do
  let fixtures := [
    buildRootNBT "" (.compound []),
    buildRootNBT "root" (.compound [
      ("byte", .byte 255), ("int", .int (-2147483648)), ("float", .float 0.8),
      ("string", .string "minecraft:overworld"), ("list", .list 3 [.int (-1), .int 256]),
      ("longs", .longArray [9223372036854775808, 9223372036854775807, 18446744073709551615])]),
    buildRootNBT "" (.compound [("MOTION_BLOCKING", .longArray (List.replicate 36 1155177711073787968))])]
  for fixture in fixtures do
    let bytes ← IO.ofExcept (fixture.mapError IO.userError)
    IO.println (String.intercalate "," (bytes.data.toList.map (toString ·)))
