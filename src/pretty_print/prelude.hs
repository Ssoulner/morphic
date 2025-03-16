import Data.Bits (Bits, (.&.), (.|.), shiftL, shiftR)
import Data.Char as C
import Data.Int (Int64, Int8)
import Data.Vector.Persistent (Vector(..))
import Data.Word (Word8)
import Distribution.Simple.Utils (xargs)
import qualified Data.Vector.Persistent as V
import System.IO.Unsafe (unsafePerformIO)

intrinsic_ByteToIntSigned :: Word8 -> Int64
intrinsic_ByteToIntSigned x = fromIntegral (fromIntegral x :: Int8)

intrinsicGet :: Vector a -> Int64 -> a
intrinsicGet xs = V.unsafeIndex xs . fromIntegral

intrinsicExtract :: Vector a -> Int64 -> (a, a -> Vector a)
intrinsicExtract xs i = (V.unsafeIndex xs i', f)
  where
    i' = fromIntegral i
    f x = V.update i' x xs

intrinsicLen :: Vector a -> Int64
intrinsicLen = fromIntegral . V.length

intrinsicPush :: Vector a -> a -> Vector a
intrinsicPush = V.snoc

intrinsicPop :: Vector a -> (Vector a, a)
intrinsicPop xs = (V.drop 1 xs, last)
  where
    last = xs `V.unsafeIndex` (V.length xs - 1)

intrinsicReserve :: Vector a -> Int64 -> Vector a
intrinsicReserve = const

intrinsicReplace :: (a -> Vector a) -> a -> Vector a
intrinsicReplace = id

shiftL_ :: Bits a => a -> Int64 -> a
shiftL_ x i = x `shiftL` fromIntegral i
shiftR_ :: Bits a => a -> Int64 -> a
shiftR_ x i = x `shiftR` fromIntegral i
_pv_string :: Vector Word8 -> String
_pv_string = V.foldr (:) [] . fmap (C.chr . fromIntegral)
_string_pv :: String -> Vector Word8
_string_pv = V.fromList . map (fromIntegral . C.ord)

class Divisible a where
  divv :: a -> a -> a
instance Divisible Int64 where
  divv = div
instance Divisible Double where
  divv = (/)

-- IO
input :: () -> Vector Word8
input _ = unsafePerformIO $ do
  line <- getLine
  return $ _string_pv line
output :: Vector Word8 -> ()
output s = unsafePerformIO $ putStr $ _pv_string s
panic :: Vector Word8 -> a
panic = error . _pv_string
