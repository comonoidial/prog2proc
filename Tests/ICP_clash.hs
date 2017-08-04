
--{-# LANGUAGE NoImplicitPrelude, #-}

module Tests.ICP_clash where


import Control.Monad
import Data.Word
--import CLaSH.Prelude (pack, unpack, shiftR,Fixed, SFixed,sf)
import CLaSH.Prelude 
--import qualified Prelude
import qualified Data.List ((++))
import Debug.Trace

import Prog2Proc.SeqLogic

topEntity = icp

type IntPart = 12
type FracPart = 15
type Number = SFixed IntPart FracPart

type VecProc s a = SeqLogic s (Vec 180 Number) (Vec 180 Number) a

icp :: VecProc s ()
icp = do
	vecPx <- receive
	clock
	vecPy <- receive
	clock
	vecQx <- receive
	clock
	vecQy <- receive
	clock
	
	vecNx <- alloc (replicate d180 (0 :: Number))
	vecNy <- alloc (replicate d180 (0 :: Number))
	vecMx <- alloc (replicate d180 (0 :: Number))
	vecMy <- alloc (replicate d180 (0 :: Number))
	
	loop 0 upto (180-1) $ \i -> do
		let pointX = vecPx!!i :: Number
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
	
	v <- alloc (replicate d4 undefined)
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
	
	--u <- allocArr 4
	u <- alloc (replicate d4 undefined)
	call $ qr v u
	
	--x <- allocArr 4
	x <- alloc (replicate d4 undefined)
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
	
--	div <- start divider
--	infuse div (-355 :: Number)
--	clock
--	infuse div (7.586)
--	clock
--	h <- alloc (replicate d180 undefined)
--	loop 44 downto 0 $ \s -> do
--		tmp <- extract div
--		let k = 44 - s
--		h?k <~ tmp
	
--	htmp <- peek h
--	h <- extract div
--	emit (replicate d180 h)
	emit (vecPx')
	clock
	emit (vecPy')


--divider :: SeqLogic s Number Number ()
--divider = do
divider :: Number -> Number -> SeqLogic s Number Number Number
divider x y = do
--	x <- receive
	let dividend	| x < 0 	= pack $ negate x
					| otherwise = pack x
	--clock -- clock between receives?
--	y <- receive
	let divisor	| y < 0 	= pack $ negate y
				| otherwise = pack y

	-- Create shift register for non-restoring division
	shiftReg <- alloc $ (++#) (pack (0 :: Number)) dividend
	-- loop length = IntPart + FracPart + FracPart
	loop 41 downto 0 $ \j -> do
		tmp <- peek shiftReg
		let shiftReg' = shiftL tmp 1
		let (r, q) = splitAtI $ bv2v shiftReg'
		let rem = v2bv r -- r, or rem is the upperhalf of the shift register
		let remN = unpack rem :: Number
		let rem'	| remN < 0 	= (rem + divisor)
					| otherwise = (rem - divisor)
		let remN' = unpack rem' :: Number
		let q0	| remN' < 0	= 0
				| otherwise = 1
		let q' = v2bv $ init q
--		let tr = "\t\t\t" ⧺ (show tmp) ⧺ "\t remN=" ⧺ (show remN) ⧺ "\t remN' =" ⧺ (show remN') ⧺ "\t q0=" ⧺ (show q0)
		let tmp1 = {-trace tr $-} (++#) rem' $ (++#) q' q0
		shiftReg <~ tmp1

	tmp2 <- peek shiftReg
	let (t, out') = splitAtI $ bv2v tmp2
	let outN = unpack (v2bv out') :: Number
--	let out' = unpack (pack $ select (snat :: SNat (IntPart + FracPart)) d1 (snat :: SNat (IntPart + FracPart)) $ bv2v tmp2) :: Number
	let neg = xor (y < 0) (x < 0) -- one of the numbers negative? negate output
	let out | neg 		= negate outN
			| otherwise = outN
	--emit (out)
	return(out)

linearSolver :: SeqLogic s Number Number ()
linearSolver = do
	--x <- allocArr 4
	x <- alloc (replicate d4 undefined)
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
--		let x_j = t / r_jj
		x_j <- call $ divider t r_jj


		x?j <~ x_j
		emit x_j
	return ()

-- 0x29FA = ⧺
xs ⧺ ys = (Data.List.++) xs ys

--qr :: Ref s (Vec n1 (Vec n2 Number)) -> Ref s (Vec n1 (Vec n1 Number)) -> VecProc s ()
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

createNormalVector ::  Number -> Number -> Number -> Number -> Number -> Number -> (Number,Number)
createNormalVector px py mx0 my0 mx1 my1 = (nx, ny) where
	(lx, ly, rx, ry)| mx0 < mx1  = (mx0, my0, mx1, my1)  -- important the the points are sorted
					| otherwise  = (mx1, my1, mx0, my0)
	check = ((rx - lx) * ( py - ly )) - ((ry - ly) * (px - lx)) -- check if point lies above or below the line through m0 and m1
	dx = lx - rx
	dy = ly - ry
	
	iSqrt = invSqrt $ dx*dx + dy*dy
	nx' = iSqrt * dx
	ny' = iSqrt * dy
	
	(nx, ny)| check == 0 = (0,0)					-- on line
			| check > 0  = (negate ny',        nx')	-- above line
			| otherwise  = (       ny', negate nx')	-- below line


--indexSmallestTwo :: KnownNat n => Vec n Number -> (Index n, Index n)
--indexSmallestTwo :: KnownNat n => Vec (n*2) Number -> (Int, Int)
indexSmallestTwo distances = (fromEnum j, fromEnum k) where 
	ids = zip distances indicesI -- [0..] -- list of tupples with (index, value)
	--(part1, part2) = splitAt (div (length distances) 2) ids  -- split in half
	(part1 :> part2 :> Nil) = transpose $  unconcat d2 ids --unconcatI ids :: Vec 2 (_x) TODO: check if this is always correct
	-- first sorting layer, the logic of the tree sorter becomes much shorter if the input can be guaranteed in order
	sortedLayer = zipWith sortTwo part1 part2 
	(_,j,_,k) = fold combineSmallestPairs sortedLayer

-- sort two points, output is (y, iy, z, iz) where y < z
sortTwo :: (Number, i) -> (Number, i) -> (Number, i, Number, i)
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
combineSmallestPairs :: (Number, i, Number, i)  -> (Number, i,  Number, i) -> (Number, i, Number, i)
combineSmallestPairs (a, ia, b, ib) (x, ix, y, iy) =
  case (a < x, b < x, a < y) of 
    (True, True, _)   -> (a, ia, b, ib)
    (True, False, _)  -> (a, ia, x, ix)
    (False, _, True)  -> (x, ix, a, ia)
    (False, _, False)  -> (x, ix, y, iy)

invSqrt x = y
--inverseRoot x = invSqrt x
	where
		x2 = shiftR x 1 -- divide by 2
		floatBitVector' = sFixedToFloatBitVector x		-- evil floating point bit level
		floatBitVector = shiftR floatBitVector' 1		-- dark evil shifting
		magic = pack (1597463007 :: Unsigned 32) - floatBitVector				-- magic
		y' = floatBitVectorToSFixed magic				-- evil floating point bit level reverse
--		y = y' * (1.5 - (x2 * y' * y'))					-- 1st iteration newton raphson
		y = y' * (1.5 - (x2 * y' * y'))					-- 1st iteration newton raphson


--sFixedToFloatBitVector converts a SFixed representation to a bitvector containing the bit reprsentation of a floating point number
sFixedToFloatBitVector :: Number -> BitVector 32 --(IntPart + FracPart)		-- NOTE: BitVector xx -> xx = int part size + frac part size ??
sFixedToFloatBitVector x = vector
	where
		x' = pack x ++# pack (repeat 0 :: Vec (FracPart + IntPart) Bit) -- Guard digits 	NOTE: (repeat 0 :: Vec xx Bit) -> xx has to be big enough to fit the entire int part size -1 shift
		lZeros = fromIntegral $ countLeadingZeros $ pack x
		shft = lZeros - (fromIntegral (snatToInteger (snat :: SNat (IntPart -1)))) -- :: Signed 5 							NOTE: (lZeros - xx) -> xx = int part size - 1
		exp = pack ( (127 - shft) :: Unsigned 9)
		mantissa' =  bv2v $ shift x' (shft)
		mantissa = v2bv $ select (snat :: SNat IntPart) d1 d23 mantissa' -- 				NOTE: (dxx d1 d23) : xx = size int part
		vector = exp ++# mantissa -- ++# pack (replicateI 0)

----floatBitVectorToSFixed convert a bitvector, which contains a 32 bit floating point representation to a SFixed representation
floatBitVectorToSFixed :: BitVector 32 -> Number
floatBitVectorToSFixed bitVector = sfixed
	where
		vector = bv2v bitVector
		exp = v2bv $ select d1 d1 d8 vector
		mantissa = select d9 d1 d23 vector
		shft' = unpack (exp - 127) :: Signed 8
		shft = fromIntegral shft'
		sfixed'' = (repeat 0 :: Vec (IntPart -1) Bit) ++ (repeat 1 :: Vec 1 Bit) ++ mantissa ++ (repeat 0 :: Vec 1 Bit) -- NOTE: (repeat 0 :: Vec xx Bit ) > xx = int part size -1
		sfixed' = bv2v $ shift (pack sfixed'') shft
		sfixed = unpack (pack $ select d0 d1 (snat :: SNat (IntPart + FracPart)) sfixed') :: Number -- NOTE: (select d0 d1 dxx sfixed') -> xx = int part size + frac part size



--invSqrt x = x

--invSqrt :: Number -> Number
--invSqrt x = y where
--  bx = pack x
--  bx2 = shiftR bx 1
--  x2 = x * 0.5
--  y' = unpack ((pack (1597463007 :: Word32)) - bx2) :: Number
--  y = y' * (1.5 - (x2 * y' * y'))

--invSqrt :: Number -> Number
--invSqrt x = do
--  let bx = pack x
--  let  bx2 = shiftR bx 1
--  let x2 = x * 0.5
--  clock
--  let y' = unpack ((pack (1597463007 :: Word32)) - bx2) :: Number
--  clock
----  y = y' * (1.5 - (x2 * y' * y'))
--  let y2' = y' * y'
--  clock
--  let x2y2 = x2 * y2'
--  clock
--  let y'' = 1.5 - x2y2
--  clock
--  return (y' * y'')

normalize :: KnownNat n => Vec (n+1) Number -> SeqLogic s i o (Vec (n+1) Number)
normalize xs = do
   let sqs = xs .*. xs
   clock
   let n = sum sqs
   clock
   let invsq = invSqrt n
   clock
   return (invsq *. xs)

dotProd :: KnownNat n => Vec (n+1) Number -> Vec (n+1) Number -> SeqLogic s i o Number
dotProd xs ys = do
   let zs = xs .*. ys
   clock
   return (sum zs)

project :: KnownNat n => Vec (n+1) Number -> Vec (n+1) Number -> SeqLogic s i o (Vec (n+1) Number)
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
