module Tests.QR4 where

import Control.Monad
import Data.List (transpose)

import Prog2Proc.SeqLogic

-- Silly factorial example component that sequentially executes only one multiplication per cycle
{-
factorial :: SeqLogic s Int Int ()
factorial = do
   n <- receive
   r <- fac n
   clock
   emit r
   clock

fac :: Int -> SeqLogic s i o Int  
fac 0 = return 1
fac n = do
   p <- fac (n-1)
   clock
   return (n * p)
-}


linFib :: SeqLogic s () Int ()
linFib = do
   n <- alloc 0
   m <- alloc 1
   loop 0 10 $ \ i -> do
      x <- use n
      y <- use m
      n <~ y
      m <~ (x + y)
   r <- use n
   emit r

linFibCo :: () -> SeqLogic s () () Int
linFibCo x = do
   n <- alloc 0
   m <- alloc 1
   loop 0 10 $ \ i -> do
      x <- use n
      y <- use m
      n <~ y
      m <~ (x + y)
   r <- use n
   return r

-- implementation of some kind of QR decomposition derived from Hendrik's masters project ICP code
qr :: SeqLogic s [Double] [[Double]] ()
qr = do
   v0 <- receive
   clock
   v1 <- receive
   clock
   v2 <- receive
   clock
   v3 <- receive
   clock
   
   let y0 = v0
   u0 <- call $ norm y0

   v1_u0 <- call $ v1 `dotp_scale` u0
   clock
   let y1 = v1 .-. v1_u0
   
   u1 <- call $ norm y1

   v2_u0 <- call $ v2 `dotp_scale` u0

   v2_u1 <- call $ v2 `dotp_scale` u1
   clock
   let sa = v2 .-. v2_u0
   clock
   let y2 = sa .-. v2_u1

   u2 <- call $ norm y2

   v3_u0 <- call $ v3 `dotp_scale` u0

   v3_u1 <- call $ v3 `dotp_scale` u1

   v3_u2 <- call $ v3 `dotp_scale` u2
   clock
   let sb = v3 .-. v3_u0
   clock
   let sc = sb .-. v3_u1
   clock
   let y3 = sc .-. v3_u2

   u3 <- call $ norm y3
   clock
   
   let q' = [u0, u1, u2, u3]

   let a = transpose [v0,v1,v2,v3]
   
   r <- call $ mat_mul q' a
   clock
   emit (transpose r)

{-
   clock
   lfc <- start $ linFibCo ()
   clock
   n <- finish lfc
   clock
   emit [[fromIntegral n]]
-}

norm :: [Double] -> SeqLogic s i o [Double]
norm xs = do
   let sqs = xs .*. xs
   clock
   let n = sum sqs
   clock
   let invsq = 1/(sqrt n)
   clock
   return (invsq *. xs)

dotp :: [Double] -> [Double] -> SeqLogic s i o Double
dotp xs ys = do
   let zs = xs .*. ys
   clock
   return (sum zs)

dotp_scale :: [Double] -> [Double] -> SeqLogic s i o [Double]
dotp_scale vs us = do
   let zs = vs .*. us
   clock
   let n = sum zs
   clock
   return (n *. us)

-- matrix multiplication using one dot product at a time
mat_mul :: [[Double]] -> [[Double]] -> SeqLogic s i o [[Double]]
mat_mul m1 m2 = do
   let m2' = transpose m2
   call $ seqMap (row_mul m1) m2'

row_mul m1 v = seqMap (dotp v) m1

-- sequentially mapping over a list using an extra cycle for each element
seqMap :: (a -> SeqLogic s i o b) -> [a] -> SeqLogic s i o [b]
seqMap f [] = return []
seqMap f (x:xs) = do
   y <- f x
   ys <- call $ seqMap f xs
   return (y:ys)

n *. xs = map (n*) xs
(.*.) = zipWith (*)
(.+.) = zipWith (+)
(.-.) = zipWith (-)
