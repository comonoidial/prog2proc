{-# LANGUAGE GADTs, Rank2Types #-}
module Prog2Proc.SeqLogic where

import Control.Applicative
import Control.Monad

import Prog2Proc.Signal
import Prog2Proc.Interpreter hiding (SeqLogic)

type SeqLogic s i o a = Program (SeqAction s i o) a

simulateSeq :: (forall s. SeqLogic s i o ()) -> [Maybe i] -> [Maybe o]
simulateSeq prog = simulate (interpretSeqLogic $ forever prog)

-- marks the boundary of a clock cycle
clock :: SeqLogic s i o ()
clock = command Clock

clocked :: a -> SeqLogic s i o a
clocked x = do
  let r = x
  clock
  return r

call :: SeqLogic s i o a -> SeqLogic s i o a
call f = do
  clock
  x <- f
  clock
  return x

inline :: SeqLogic s i o a -> SeqLogic s i o a
inline f = f

-- tries to read a value from external input or block
receive :: SeqLogic s a o a
receive = command Receive

-- send a result to the external output
emit :: a -> SeqLogic s i a ()
emit = command . Emit

type Ref s a = Reference s a

alloc :: a -> SeqLogic s i o (Ref s a)
alloc = command . Alloc

allocArr :: Int -> SeqLogic s i o (Ref s [a])
allocArr = command . AllocArr

peek :: Ref s a -> SeqLogic s i o a
peek = command . Load

infixr 1 <~
(<~) :: Ref s a -> a -> SeqLogic s i o ()
(<~) p x = command (Store p x)

infixl 4 ?
(?) :: Ref s [a] -> Int -> Ref s a
r ? i = indexRef i r

start :: SeqLogic s j p a -> SeqLogic s i o (Coproc s j p a)
start = command . Start

finish :: Coproc s j p a -> SeqLogic s i o a
finish = command . Finish

inject :: Coproc s j p x -> j -> SeqLogic s i o ()
inject c x = command (Infuse c x)

extract :: Coproc s j a x -> SeqLogic s i o a
extract = command . Extract

data LoopDir = Up | Down

upto = Up
downto = Down

loop :: (Enum k, Ord k) => k -> LoopDir -> k -> (k -> SeqLogic s i o ()) -> SeqLogic s i o ()
loop n Up m body 
  | n <= m     = clock >> body n >> loop (succ n) Up m body
  | otherwise = clock >> return ()
loop n Down m body 
  | n >= m     = clock >> body n >> loop (pred n) Down m body
  | otherwise = clock >> return ()

mapS :: (a -> b) -> [[a]] -> SeqLogic s i o [[b]]
mapS f [] = return []
mapS f (x:xs) = do
   clock
   let y = map f x
   ys <- mapS f xs
   return (y:ys)

zipWithS :: (a -> b -> c) -> [[a]] -> [[b]] -> SeqLogic s i o [[c]]
zipWithS f (x:xs) (y:ys) = do
   clock
   let z = zipWith f x y
   zs <- zipWithS f xs ys
   return (z:zs)

foldS :: (b -> a -> b) -> b -> [[a]] -> SeqLogic s i o b
foldS f z [] = return z
foldS f z (x:xs) = do
   clock
   let y = foldl f z x
   foldS f y xs

-- v <^ f = liftM2 f v
-- f ^> v = f v