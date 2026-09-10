{-# LANGUAGE OverloadedStrings #-}
import Ibis.Compiler.Debugger.NBT
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy as BS
import Data.List (intercalate)

main :: IO ()
main = mapM_ (putStrLn . intercalate "," . map show . BS.unpack . toLazyByteString)
  [ buildRootNBT "" (TagCompound [])
  , buildRootNBT "root" (TagCompound
      [("byte", TagByte 255), ("int", TagInt (-2147483648)), ("float", TagFloat 0.8),
       ("string", TagString "minecraft:overworld"), ("list", TagList 3 [TagInt (-1), TagInt 256]),
       ("longs", TagLongArray [minBound, maxBound, -1])])
  , buildRootNBT "" (TagCompound [("MOTION_BLOCKING", TagLongArray (replicate 36 1155177711073787968))])
  ]
