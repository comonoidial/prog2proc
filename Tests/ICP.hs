module Tests.ICP where

import Control.Monad
import Data.List (transpose)

import Prog2Proc.SeqLogic

icp :: SeqLogic s [Double] [[Double]] ()
icp = do
	px <- receive
	clock
	py <- receive
	clock
	qx <- receive
	clock
	qy <- receive
	clock

	nx <- alloc (replicate 180 undefined)
	ny <- alloc (replicate 180 undefined)
	mx <- alloc (replicate 180 undefined)
	my <- alloc (replicate 180 undefined)

	loop 0 (180-1) $ \ i -> do
		-- get i'th value of px and replicate
		let pxri = replicate 180 (px!!i)
		let dx = pxri .-. qx
		clock
		let dx2 = dx .*. dx
		clock
		-- get i'th value of py and replicate
		let pyri = replicate 180 (py!!i)
		let dy = pyri .-. qy
		clock
		let dy2 = dy .*. dy
		clock
		let dx2dy2 = dy .+. dx
		clock
		let s = smallestDistance dx2dy2
		-- left to do -> s is smallest distance, get the corresponding qx and qy coordinate, 
		mx?i <~ sqx -- and place them in the m vector on the i'th location
		clock
		my?i <~ sqy
		-- also create an normal vector place the nx

		nx?i <~ normx  -- place the nx and ny in the i'th location of the n vector
		clock
		ny?i <~ normy

	v0 <- use nx
	clock
	v1 <- use ny
	clock
	let v2'' = px .*. nx
	clock
	let v2'  = py .*. ny
	clock
	let v2   = v2' .+. v2''
	clock
	let v3'' = px .*. ny
	clock
	let v3'  = py .*. nx
	clock
	let v3   = v3' .+. v3''
	clock
	let b'' = mx .*. nx
	clock
	let b'  = my .*. ny
	clock
	let b   = b' .+. b''
	clock
	([u0, u1, u2, u3],r) <- call $ qr [v0,v1,v2,v3] -- r is the 4x4 upper triangluar matrix, q is 180x4
--	let [u0, u1, u2, u3] = q'
	clock
--	t <- call $ mat_mul q' b -- t is the 4x1 vector of the sytem rx = t
	t0 <- call $ u0 `dotp` b
	clock
	t1 <- call $ u1 `dotp` b
	clock
	t2 <- call $ u2 `dotp` b
	clock
	t3  <- call $ u3 `dotp` b
	clock


linSolver r [t0,t1,t2,t3] = do
	-- x3 = t3/r33
	let x3 = t3 / r33
	clock

	-- x2 = (t2-r23*x3)/r22	
	let r23x3	= r23 * x3
	clock
	let cx2'		= t2 - r23x3
	clock
	let x2		= x2' / r22
	clock

	-- x1 = (t1 - r12x2 - r13x3) / r11
	let r12x2 = r12 * x2
	clock
	let r13x3 = r13 * x3
	clock
	let x1'' = t1 - r12x2
	clock
	let x1' = x1'' - r13x3
	clock
	let cx1 = x1' / r11
	clock

	-- x0 = (t0 - r01x1 - r02x2 - r03x3) / r00
	let r01x1 = r01 * x1
	clock
	let r02x2 = r02 * x2
	clock
	let r03x3 = r03 * x3
	clock
	let x0''' = t1    - r01x1
	clock
	let x0'' = x0''' - r02x2
	clock
	let x0' = x0'   - r03x3
	clock
	let x0 = x0' / r00
	clock
	return [x0,x1,x2,x3]


-- implementation of some kind of QR decomposition derived from Hendrik's masters project ICP code
qr :: SeqLogic s [Double] [[Double]] ()
qr [v0,v1,v2,v3] = do
   
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
   return (q',r)

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
