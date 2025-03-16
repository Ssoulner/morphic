module Main where

import Data.Word (Word8)
import Data.Bits (Bits, (.&.), (.|.), shiftL, shiftR, xor)
import Data.Int (Int64, Int8)
import Data.Char as C
import System.IO.Unsafe (unsafePerformIO)

intrinsic_ByteToIntSigned :: Word8 -> Int64
intrinsic_ByteToIntSigned x = fromIntegral (fromIntegral x :: Int8)

intrinsicGet :: [a] -> Int64 -> a
intrinsicGet xs = (!!) xs . fromIntegral
intrinsicExtract :: [a] -> Int64 -> (a, a -> [a])
intrinsicExtract xs i = let i' = fromIntegral i 
                        in  (xs !! i', \x -> take i' xs ++ [x] ++ drop (i'+1) xs)
intrinsicLen :: [a] -> Int64
intrinsicLen = fromIntegral . length
intrinsicPush :: [a] -> a -> [a]
intrinsicPush xs x = xs ++ [x]
intrinsicPop :: [a] -> ([a], a)
intrinsicPop xs = (init xs, last xs)
intrinsicReserve :: [a] -> Int64 -> [a]
intrinsicReserve xs _ = xs
intrinsicReplace :: (a -> [a]) -> a -> [a]
intrinsicReplace f x = f x
shiftL_ :: Bits a => a -> Int64 -> a
shiftL_ x i = x `shiftL` fromIntegral i
shiftR_ :: Bits a => a -> Int64 -> a
shiftR_ x i = x `shiftR` fromIntegral i
_pv_string :: [Word8] -> String
_pv_string = map (C.chr . fromIntegral)
_string_pv :: String -> [Word8]
_string_pv = map (fromIntegral . C.ord)

class Divisible a where
  divv :: a -> a -> a
instance Divisible Int64 where
  divv = div
instance Divisible Double where
  divv = (/)

-- IO
input :: () -> [Word8]
input _ = unsafePerformIO $ do
  line <- getLine
  return $ _string_pv line
output :: [Word8] -> ()
output s = unsafePerformIO $ putStr $ _pv_string s
panic :: [Word8] -> a
panic = error . _pv_string
