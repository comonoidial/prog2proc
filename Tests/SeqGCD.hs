module Tests.SeqGCD where

import Data.Bits
import Data.Word

import Prog2Proc.SeqLogic

runGCD :: SeqLogic s Word32 Word32 ()
runGCD = do
  x <- receive
  clock
  y <- receive
  r <- call $ binGCD x y
  emit r
  return ()

binGCD :: Word32 -> Word32 -> SeqLogic s Word32 Word32 Word32
binGCD x y = do
  let isZero = y == 0
  clock
  if isZero then return x
  else do
    a <- call $ dropZeros x
    b <- call $ dropZeros y
    let g = max a b
    clock
    let s = min a b
    clock
    let d = g - s
    r <- call $ binGCD s d
    let o = x .|. y
    e <- call $ countZeros o
    return (r <<< e)

dropZeros :: Word32 -> SeqLogic s Word32 Word32 Word32
dropZeros i = do
  s <- call $ countZeros i
  return (i >>> s)

countZeros :: Word32 -> SeqLogic s Word32 Word32 Word32
countZeros n = do
  let isOdd = odd n
  clock
  if isOdd then return 0 
  else do
    let m = n >>> 1
    c <- call $ countZeros m
    return (c + 1)

infixl 8 >>>
(>>>) :: (Bits a,Integral b) => a -> b -> a
x >>> s = x `shiftR` fromIntegral s
infixl 8 <<<
(<<<) :: (Bits a,Integral b) => a -> b -> a
x <<< s = x `shiftL` fromIntegral s
