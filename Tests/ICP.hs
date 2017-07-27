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
    let vecDx2 = vecDx .*. vecDx
    clock
    let vecDy2 = vecDy .*. vecDy
    clock
    let vecSquaredDist = vecDx2 .+. vecDy2
    clock
    let (j,k) = indexSmallestTwo vecSquaredDist
    clock
    let mx0 = vecQx!!j
    let mx1 = vecQx!!k
    clock
    let my0 = vecQy!!j
    let my1 = vecQy!!k
    clock
    let (nx, ny) = createNormalVector pointX pointY mx0 my0 mx1 my1
    clock
    vecMx?i <~ mx0
    clock
    vecMy?i <~ my0
    clock
    vecNx?i <~ nx
    clock
    vecNy?i <~ ny

  v <- allocArr 4
  v0 <- peek vecNx
  v?0 <~ v0
  clock
  v1 <- peek vecNy
  v?1 <~ v1
  clock
  let v2'' = vecPx .*. v0
  clock
  let v2'  = vecPy .*. v1
  clock
  v?2 <~ v2' .+. v2''
  clock
  let v3'' = vecPx .*. v1
  clock
  let v3'  = vecPy .*. v0
  clock
  v?3 <~ v3'' .-. v3'
  clock
  vecMx' <- peek vecMx
  let b'' = vecMx' .*. v0
  clock
  vecMy' <- peek vecMy
  let b'  = vecMy' .*. v1
  clock
  let b   = b' .+. b''

  u <- allocArr 4
  call $ qr v u

  x <- allocArr 4
  linSolv <- start linearSolver
  loop 3 downto 0 $ \j -> do
     u_j <- peek (u?j)
     t_j <- inline $ u_j `dotProd` b
     infuse linSolv t_j
     loop 3 downto j $ \k -> do
        v_k <- peek (v?k)
        r_jk <- inline $ u_j `dotProd` v_k
        infuse linSolv r_jk
     x_j <- extract linSolv
     x?j <~ x_j
  finish linSolv
  
  transX <- peek (x?0)
  clock
  transY <- peek (x?1)
  clock
  cosTh <- peek (x?2)
  clock
  sinTh <- peek (x?3)
  clock
  let vecPxCt = cosTh *. vecPx
  clock
  let vecPySt = sinTh *. vecPy
  clock
  let vecPxCtPySt = vecPxCt .-. vecPySt
  clock
  let vecPx' = transX +. vecPxCtPySt
  clock
  let vecPyCt = cosTh *. vecPy
  clock
  let vecPxSt = sinTh *. vecPx
  clock
  let vecPyCtPxSt = vecPyCt .+. vecPxSt
  clock
  let vecPy' = transY +. vecPyCtPxSt
  clock

  emit (vecPx')
  clock
  emit (vecPy')

linearSolver :: SeqLogic s Float Float ()
linearSolver = do
  x <- allocArr 4
  loop 3 downto 0 $ \j -> do
     t_j <- receive
     tmp <- alloc t_j
     loop 3 downto (j+1) $ \k -> do
        r_jk <- receive
        x_k <- peek (x?k)
        let rx = r_jk * x_k
        clock
        t <- peek tmp
        tmp <~ t - rx
     r_jj <- receive
     t <- peek tmp
     let x_j = t / r_jj
     x?j <~ x_j
     emit x_j
  return ()

qr :: Ref s [[Float]] -> Ref s [[Float]] -> SeqLogic s [Float] [Float] ()
qr v u = do
  loop 0 upto 3 $ \j -> do
     v_j <- peek (v?j)
     tmp <- alloc v_j
     loop 0 upto (j-1) $ \k -> do
        u_k <- peek (u?k)
        vj_uk <- inline $ v_j `project` u_k
        clock
        t <- peek tmp
        tmp <~ t .-. vj_uk
     t <- peek tmp
     u_j <- inline $ normalize t
     u?j <~ u_j
  return ()

createNormalVector ::  Float -> Float -> Float -> Float -> Float -> Float -> (Float,Float)
createNormalVector px py mx0 my0 mx1 my1 = (nx, ny) where
  (lx, ly, rx, ry)   | mx0 < mx1  = (mx0, my0, mx1, my1)  -- important the the points are sorted
            | otherwise  = (mx1, my1, mx0, my0)
  check = ((rx - lx) * ( py - ly )) - ((ry - ly) * (px - lx)) -- check if point lies above or below the line through m0 and m1
  dx = lx - rx
  dy = ly - ry

  iSqrt = invSqrt $ dx*dx + dy*dy
  nx' = iSqrt * dx
  ny' = iSqrt * dy

  (nx, ny)  | check == 0  = (0,0)             -- on line
        | check > 0    = (negate ny',        nx')  -- above line
        | otherwise   = (       ny', negate nx')  -- below line


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
