module Clash.BINGCD_COPROC where

import Control.Monad
import Data.Word
--import CLaSH.Prelude (pack, unpack, shiftR,Fixed, SFixed,sf)
--import qualified Prelude
import Debug.Trace
import CLaSH.Prelude hiding ((++), replicate)
import Data.List ((++), replicate)

import Prog2Proc.SeqLogic

type IntPart = 12
type FracPart = 15
--type Number = SFixed IntPart FracPart
type Number = Word32


testBINGCD x y = simulateSeq system ([Just x, Just y] ++ replicate 500 Nothing)

system :: SeqLogic s Number Number ()
system = do
	x <- receive
	clock
	y <- receive
	clock
	gcd <- start binGCD
	infuse gcd x
	clock
	infuse gcd y
	clock
	z <- extract gcd
	emit z

binGCD :: SeqLogic s Number Number ()
binGCD = do
	n1 <- receive
	clock
	n2 <- receive
	clock
	x_ <- alloc n1
	y_ <- alloc n2
	e_ <- alloc 0
	loop 15 downto 0 $ \k -> do
		x <- peek x_
		let a = dropTrailingZeros x
		clock
		y <- peek y_
		let b = dropTrailingZeros y
		clock
		let g = max a b
		clock
		let s = min a b
		clock
		let d = g - s
		clock
		let o = x .|. y
		clock
		let tz = countTrailingZeros o
		clock
		--let t0 = "\n g=" ++ (show g) ++ "\t s=" ++ (show s) ++ "\t tz=" ++ (show tz) ++ "\t e=" ++ (show e) ++ "\n"
		e <- peek e_
		let e' = {-trace t0 $-} e + tz
		e_ <~ e'
		x_ <~ s
		y_ <~ d


	sh <- peek e_
	r <- peek y_  -- or y?
	clock
	let out = r `shiftL` sh
	emit (out)

dropTrailingZeros :: Number -> Number
dropTrailingZeros i = i `shiftR` countTrailingZeros i

