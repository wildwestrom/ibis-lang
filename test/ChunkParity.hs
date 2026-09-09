import Data.Serialization
import qualified Data.ByteString as BS
import Data.List (intercalate)

main :: IO ()
main = mapM_ check
  [ SerializedChunk 0 0 0 0 [] BS.empty
  , SerializedChunk (-1) 2 (-3) 4 [0x0102030405060708] (BS.pack [0, 255])
  , SerializedChunk minBound maxBound 0 (-1) [0, maxBound, 256] (BS.pack [73, 66, 73, 83])
  ]
  where
    check chunk = do
      let bytes = serializeChunk chunk
      case deserializeChunk bytes of
        Left err -> fail err
        Right decoded
          | serializeChunk decoded == bytes -> putStrLn (intercalate "," (map show (BS.unpack bytes)))
          | otherwise -> fail "chunk round trip failed"
