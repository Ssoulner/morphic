module Main where

import Data.Word (Word8)
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.Int (Int64, Int8)
import Data.Char as C

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
_pv_string :: [Word8] -> String
_pv_string = map (C.chr . fromIntegral)
_string_pv :: String -> [Word8]
_string_pv = map (fromIntegral . C.ord)

-- IO
input :: () -> [Word8]
input _ = undefined
output :: [Word8] -> IO ()
output = putStrLn . _pv_string
panic :: [Word8] -> a
panic = error . _pv_string