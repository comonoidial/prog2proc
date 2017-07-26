module Tests.ICP where

import Control.Monad
import Data.List (transpose)
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

	loop 0 (180-1) $ \i -> do
		-- get i'th value of px and replicate
		let pointX = vecPx!!i
		let vecPointX = replicate 180 pointX
		let vecDx = vecPointX .-. vecQx
		clock
		-- get i'th value of py and replicate
		let pointY = vecPy!!i
		let vecPointY = replicate 180 pointY
		let vecDy = vecPointY .-. vecQy
		clock
		let vecDx2 = vecDx .*. vecDx
		clock
		let vecDy2 = vecDy .*. vecDy
		clock
		let vecSquaredDist = vecDx2 .+. vecDy2
		clock
		let (j,k) = sortTree vecSquaredDist
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
	v0 <- use vecNx
	v?0 <~ v0
	clock
	v1 <- use vecNy
	v?1 <~ v1
	clock
	let v2'' = vecPx .*. v0
	clock
	let v2'  = vecPy .*. v1
	clock
	let v2   = v2' .+. v2''
	v?2 <~ v2
	clock
	let v3'' = vecPx .*. v1
	clock
	let v3'  = vecPy .*. v0
	clock
	let v3   = v3'' .-. v3'
	v?3 <~ v3
	clock
	vecMx' <- use vecMx
	let b'' = vecMx' .*. v0
	clock
	vecMy' <- use vecMy
	let b'  = vecMy' .*. v1
	clock
	let b   = b' .+. b''
	[u0, u1, u2, u3] <- call $ qr [v0,v1,v2,v3] -- r is the 4x4 upper triangluar matrix, q is 180x4
	u <- allocArr 4
--	t <- call $ mat_mul q' b -- t is the 4x1 vector of the sytem rx = t
	u?0 <~ u0
	clock
	u?1 <~ u1
	clock
	u?2 <~ u2
	clock
	u?3 <~ u3
	clock
	x <- allocArr 4
	linSolv <- start linearSolver
	loop 0 3 $ \j' -> let j = 3-j' in do
		u_j <- use (u?j)
		t_j <- call $ u_j `dotp` b
		infuse linSolv t_j
		loop 0 j' $ \k' -> let k = 3-k' in do
			v_k <- use (v?k)
			r_jk <- call $ u_j `dotp` v_k
			infuse linSolv r_jk
		x_j <- extract linSolv
		x?j <~ x_j
	finish linSolv
	tx <- use (x?0) -- x0 = tx
	clock
	ty <- use (x?1) -- x1 = ty
	clock
	ct <- use (x?2) -- x2 = cos theta = ct
	clock
	st <- use (x?3) -- x3 = sin theta = st 
	clock
	-- vecPx' = vecPx * ct - vecPy * st + tx
	-- vecPy' = vecPy * ct + vecPx * st + ty
	let vecPxCt = ct *. vecPx
	clock
	let vecPySt = st *. vecPy
	clock
	let vecPxCtPySt = vecPxCt .-. vecPySt
	clock
	let vecPx' = tx +. vecPxCtPySt
	clock

	let vecPyCt = ct *. vecPy
	clock
	let vecPxSt = st *. vecPx
	clock
	let vecPyCtPxSt = vecPyCt .+. vecPxSt
	clock
	let vecPy' = ty +. vecPyCtPxSt
	clock

	emit (vecPx')
	clock
	emit (vecPy')

linearSolver :: SeqLogic s Float Float ()
linearSolver = do
	-- x3 = t3/r33
	t3 <- receive
	clock
	r33 <- receive
	let x3 = t3 / r33
	emit x3
	clock

	-- x2 = (t2-r23*x3)/r22	
	t2 <- receive
	clock
	r23 <- receive
	let r23x3 = r23 * x3
	clock
	let x2' = t2 - r23x3
	clock
	r22 <- receive
	let x2 = x2' / r22
	emit x2
	clock

	-- x1 = (t1 - r12x2 - r13x3) / r11
	t1 <- receive
	clock
	r13 <- receive
	let r13x3 = r13 * x3
	clock
	r12 <- receive
	let r12x2 = r12 * x2
	clock
	let x1'' = t1 - r12x2
	clock
	let x1' = x1'' - r13x3
	clock
	r11 <- receive
	let x1 = x1' / r11
	emit x1
	clock

	-- x0 = (t0 - r01x1 - r02x2 - r03x3) / r00
	t0 <- receive
	clock
	r03 <- receive
	let r03x3 = r03 * x3
	clock
	r02 <- receive
	let r02x2 = r02 * x2
	clock
	r01 <- receive
	let r01x1 = r01 * x1
	clock
	let r02x2 = r02 * x2
	clock
	let x0''' = t0 - r01x1
	clock
	let x0'' = x0''' - r02x2
	clock
	let x0' = x0'' - r03x3
	clock
	r00 <- receive
	let x0 = x0' / r00
	emit x0
	return ()

qr :: [[Float]] -> SeqLogic s [Float] [Float] [[Float]]
qr [v0,v1,v2,v3] = do
	let y0 = v0
	u0 <- call $ norm y0
	clock

	v1_u0 <- call $ v1 `dotp_scale` u0
	let y1 = v1 .-. v1_u0
	clock
	u1 <- call $ norm y1
	clock

	v2_u0 <- call $ v2 `dotp_scale` u0
	v2_u1 <- call $ v2 `dotp_scale` u1
	let sa = v2 .-. v2_u0
	clock
	let y2 = sa .-. v2_u1
	clock
	u2 <- call $ norm y2
	
	v3_u0 <- call $ v3 `dotp_scale` u0
	v3_u1 <- call $ v3 `dotp_scale` u1
	v3_u2 <- call $ v3 `dotp_scale` u2
	let sb = v3 .-. v3_u0
	clock
	let sc = sb .-. v3_u1
	clock
	let y3 = sc .-. v3_u2
	clock
	u3 <- call $ norm y3

	return [u0, u1, u2, u3]

createNormalVector ::  Float -> Float -> Float -> Float -> Float -> Float -> (Float,Float)
createNormalVector px py mx0 my0 mx1 my1 = (nx, ny) where
	(lx, ly, rx, ry) 	| mx0 < mx1	= (mx0, my0, mx1, my1)	-- important the the points are sorted
						| otherwise	= (mx1, my1, mx0, my0)
	check = ((rx - lx) * ( py - ly )) - ((ry - ly) * (px - lx)) -- check if point lies above or below the line through m0 and m1
	dx = lx - rx
	dy = ly - ry

	iSqrt = invSqrt $ dx*dx + dy*dy
	nx' = iSqrt * dx
	ny' = iSqrt * dy

	(nx, ny)	| check == 0	= (0,0)					 	-- on line
				| check > 0		= (negate ny',        nx')	-- above line
				| otherwise 	= (       ny', negate nx')	-- below line


sortTree :: [Float] -> (Int, Int)
sortTree distances = (j,k) where 
	ids = zip distances [0..] -- list of tupples with (index, value)
	(part1, part2) = splitAt (div (length distances) 2) ids	-- split in half
	-- first sorting layer, the logic of the tree sorter becomes much shorter if the input can be guaranteed in order
	sortedLayer = zipWith (closestOfTwoPoints) part1 part2 
	(_,j,_,k) = foldl1 (closestTwoOfFourPoints) sortedLayer
	

-- sort two points, output is (y, iy, z, iz) where y < z
closestOfTwoPoints :: (Float, i) -> (Float, i) -> (Float, i, Float, i)
closestOfTwoPoints (a, ia) (x, ix) 
	| a < x 	= (a, ia, x, ix)
	| otherwise = (x, ix, a, ia) 


-- find the two closest distances with index out of four distances, this function can be used in a tree structure find the two closest points out a list of points
-- NOTE: the input tuples have to be sorted already, so a < b, and x < y
-- with a < b and x < y the following outcomes are possible -> since were only interested in the two smallest ones some logic can be extracted
-- a < b < x < y	-> b < x
-- a < x < b < y	-> a < x
-- a < x < y < b	-> a < x
-- x < a < b < y	-> x < a
-- x < a < y < b	-> x < a
-- x < y < a < b	-> a < y
closestTwoOfFourPoints :: (Float, i, Float, i)  -> (Float, i,  Float, i) -> (Float, i, Float, i)
closestTwoOfFourPoints (a, ia, b, ib) (x, ix, y, iy) =
	case (a < x, b < x, a < y) of 
		(True, True, _) 	-> (a, ia, b, ib)
		(True, False, _)	-> (a, ia, x, ix)
		(False, _, True)	-> (x, ix, a, ia)
		(False, _, False)	-> (x, ix, y, iy)


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
--	let bx = pack x
--	let	bx2 = shiftR bx 1
--	let x2 = x * 0.5
--	clock
--	let y' = unpack ((pack (1597463007 :: Word32)) - bx2) :: Float
--	clock
----	y = y' * (1.5 - (x2 * y' * y'))
--	let y2' = y' * y'
--	clock
--	let x2y2 = x2 * y2'
--	clock
--	let y'' = 1.5 - x2y2
--	clock
--	return (y' * y'')

norm :: [Float] -> SeqLogic s i o [Float]
norm xs = do
   let sqs = xs .*. xs
   clock
   let n = sum sqs
   clock
   let invsq = invSqrt n
   clock
   return (invsq *. xs)

dotp :: [Float] -> [Float] -> SeqLogic s i o Float
dotp xs ys = do
   let zs = xs .*. ys
   clock
   return (sum zs)

dotp_scale :: [Float] -> [Float] -> SeqLogic s i o [Float]
dotp_scale vs us = do
   let zs = vs .*. us
   clock
   let n = sum zs
   clock
   return (n *. us)

n *. xs = map (n*) xs
n +. xs = map (+n) xs
(.*.) = zipWith (*)
(.+.) = zipWith (+)
(.-.) = zipWith (-)
