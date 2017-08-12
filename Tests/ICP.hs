module Tests.ICP where

import Control.Monad
import Data.Word
--import CLaSH.Prelude (pack, unpack, shiftR)

import Prog2Proc.SeqLogic

icp :: SeqLogic s [Float] [Float] ()
icp = do
  vecPx <- receive
  clock
  vecPy <- receive
  clock
  vecQx <- receive
  clock
  vecQy <- receive
  clock

  vecNx <- alloc (replicate 180 undefined)
  vecNy <- alloc (replicate 180 undefined)
  vecMx <- alloc (replicate 180 undefined)
  vecMy <- alloc (replicate 180 undefined)

  loop 0 upto (180-1) $ \i -> do
    let pointX = vecPx!!i
    let vecDx = pointX -. vecQx
    clock
    let pointY = vecPy!!i
    let vecDy = pointY -. vecQy
    clock
    vecMagSq <- vecDx.*.vecDx |^(.+.)^| vecDy.*.vecDy
    clock
    let (j,k) = indexSmallestTwo vecMagSq
    normLV <- start normLineVec
    clock
    let px  = vecPx!!i
    let mxA = vecQx!!j
    let mxB = vecQx!!k
    inject normLV (px, mxA, mxB)
    vecMx?i <~ mxA
    clock
    let py  = vecPy!!i
    let myA = vecQy!!j
    let myB = vecQy!!k
    inject normLV (py, myA, myB)
    vecMy?i <~ myA
    clock
    vecNx?i <~< extract normLV
    clock
    vecNy?i <~< finish normLV

  v <- allocArr 4
  v0 <- peek vecNx
  v?0 <~ v0
  clock
  v1 <- peek vecNy
  v?1 <~ v1
  clock
  v?2 <~< vecPy.*.v1 |^(.+.)^| vecPx.*.v0
  clock
  v?3 <~< vecPx.*.v1 |^(.-.)^| vecPy.*.v0
  clock
  vecMx' <- peek vecMx
  let b'' = vecMx' .*. v0
  clock
  vecMy' <- peek vecMy
  let b' = vecMy' .*. v1
  clock
  let b = b' .+. b''

  u <- call $ gram_schmidt v

  x <- allocArr 4
  linSolv <- start linearSolver
  loop 3 downto 0 $ \j -> do
     u_j <- peek (u?j)
     t_j <- inline $ u_j `dotProd` b
     inject linSolv t_j
     loop 3 downto j $ \k -> do
        v_k <- peek (v?k)
        r_jk <- inline $ u_j `dotProd` v_k
        inject linSolv r_jk
     x?j <~< extract linSolv
  finish linSolv
  
  transX <- peek (x?0)
  clock
  transY <- peek (x?1)
  clock
  cosTh <- peek (x?2)
  clock
  sinTh <- peek (x?3)
  clock
  vecRotX <- cosTh*.vecPx |^(.-.)^| sinTh*.vecPy
  clock
  let vecPx' = transX +. vecRotX
  clock
  vecRotY <- cosTh*.vecPy |^(.+.)^| sinTh*.vecPx
  clock
  let vecPy' = transY +. vecRotY
  clock

  emit (vecPx')
  clock
  emit (vecPy')

linearSolver :: SeqLogic s Float Float ()
linearSolver = do
  x <- allocArr 4
  loop 3 downto 0 $ \j -> do
     t_j <- receive
     t <- loopAccum (3, downto, j+1) t_j $ \k t -> do
        r_jk <- receive
        x_k <- peek (x?k)
        let rx = r_jk * x_k
        clock
        return (t - rx)
     r_jj <- receive
     let x_j = t / r_jj
     x?j <~ x_j
     emit x_j
  return ()

gram_schmidt :: Ref s [[Float]] -> SeqLogic s [Float] [Float] (Ref s [[Float]])
gram_schmidt v = do
  u <- allocArr 4
  loop 0 upto 3 $ \j -> do
     v_j <- peek (v?j)
     t <- loopAccum (0, upto , j-1) v_j $ \k t -> do
        u_k <- peek (u?k)
        vj_uk <- inline $ v_j `project` u_k
        clock
        return (t .-. vj_uk)
     u?j <~< inline $ normalize t
  return u

normLineVec :: SeqLogic s (Float, Float, Float) Float Float
normLineVec = do
  (px, mxA, mxB) <- receive
  let dx = mxB - mxA
  let sdx = dx*dx
  let pxmA = px - mxA
  clock
  (py, myA, myB) <- receive
  let dy = myB - myA
  let sdy = dy*dy
  let pymA = py - myA
  clock
  let check = (dx * pymA) - (dy * pxmA) -- check if point lies above or below the line through m0 and m1
  let iSqrt = invSqrt $ sdx + sdy
  clock
  let nx' = iSqrt * dx
  let ny' = iSqrt * dy
  let (nx, ny) = if (check == 0) then (0,0) else
       if (check > 0) == (dx > 0)
         then (negate ny',        nx')
         else (       ny', negate nx')
  emit nx
  return ny

indexSmallestTwo :: [Float] -> (Int, Int)
indexSmallestTwo distances = (j,k) where 
  ids = zip distances [0..] -- list of tupples with (index, value)
  (part1, part2) = splitAt (div (length distances) 2) ids  -- split in half
  -- first sorting layer, the logic of the tree sorter becomes much shorter if the input can be guaranteed in order
  sortedLayer = zipWith sortTwo part1 part2 
  (_,j,_,k) = foldl1 combineSmallestPairs sortedLayer

-- sort two points, output is (y, iy, z, iz) where y < z
sortTwo :: (Float, i) -> (Float, i) -> (Float, i, Float, i)
sortTwo (a, ia) (x, ix) 
  | a < x   = (a, ia, x, ix)
  | otherwise = (x, ix, a, ia) 

-- find the two closest distances with index out of four distances, this function can be used in a tree structure find the two closest points out a list of points
-- NOTE: the input tuples have to be sorted already, so a < b, and x < y
-- with a < b and x < y the following outcomes are possible -> since were only interested in the two smallest ones some logic can be extracted
-- a < b < x < y  -> b < x
-- a < x < b < y  -> a < x
-- a < x < y < b  -> a < x
-- x < a < b < y  -> x < a
-- x < a < y < b  -> x < a
-- x < y < a < b  -> a < y
combineSmallestPairs :: (Float, i, Float, i)  -> (Float, i,  Float, i) -> (Float, i, Float, i)
combineSmallestPairs (a, ia, b, ib) (x, ix, y, iy) =
  case (a < x, b < x, a < y) of 
    (True, True, _)   -> (a, ia, b, ib)
    (True, False, _)  -> (a, ia, x, ix)
    (False, _, True)  -> (x, ix, a, ia)
    (False, _, False)  -> (x, ix, y, iy)


invSqrt x = 1/(sqrt x)
{-
invSqrt :: Float -> Float
invSqrt x = y where
  bx = pack x
  bx2 = shiftR bx 1
  x2 = x * 0.5
  y' = unpack ((pack (1597463007 :: Word32)) - bx2) :: Float
  y = y' * (1.5 - (x2 * y' * y'))
-}
--invSqrt :: Float -> Float
--invSqrt x = do
--  let bx = pack x
--  let  bx2 = shiftR bx 1
--  let x2 = x * 0.5
--  clock
--  let y' = unpack ((pack (1597463007 :: Word32)) - bx2) :: Float
--  clock
----  y = y' * (1.5 - (x2 * y' * y'))
--  let y2' = y' * y'
--  clock
--  let x2y2 = x2 * y2'
--  clock
--  let y'' = 1.5 - x2y2
--  clock
--  return (y' * y'')

normalize :: [Float] -> SeqLogic s i o [Float]
normalize xs = do
   let sqs = xs .*. xs
   clock
   let n = sum sqs
   clock
   let invsq = invSqrt n
   clock
   return (invsq *. xs)

dotProd :: [Float] -> [Float] -> SeqLogic s i o Float
dotProd xs ys = do
   let zs = xs .*. ys
   clock
   return (sum zs)

project :: [Float] -> [Float] -> SeqLogic s i o [Float]
project vs us = do
   let zs = vs .*. us
   clock
   let n = sum zs
   clock
   return (n *. us)

n *. xs = map (n*) xs
n +. xs = map (n+) xs
n -. xs = map (n-) xs
(.*.) = zipWith (*)
(.+.) = zipWith (+)
(.-.) = zipWith (-)
