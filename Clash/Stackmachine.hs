module StackMachine where
import CLaSH.Prelude
import Data.Bits
import Data.Word
import Debug.Trace

data Label = I0 | I1 | GCD | T1 | E1 | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DZs | CE | N7 | CZs | T2 | E2 | N8 | CF | N9 
	deriving (Enum,Show)

instance Default Label where
	def = I0

data Ctrl = NextPC | Return | CondSkip | Call Label
data Oper = Cnst  | Plus | Sub | Or | Min | Max | ShR | ShL | IsEq | IsOdd deriving Show
data Input = S Word8 | I Word32
data StAction = SNop | Push | PushAfterPop Word8

selInput :: Word32 -> Input -> Word32
selInput a (S _) = a
selInput _ (I x) = x

agu :: Word8 -> Input -> Word8
agu stackSp (S i) = stackSp - i
agu stackSp (I _) = stackSp

ctrl :: Ctrl -> Word32 -> Label -> Word8 -> Label -> (Word8, Maybe (Word8, Label), Label)
ctrl NextPC		_ pc rdAddr ctrlStack = (rdAddr  , Nothing					, succ pc		)
ctrl Return		_ pc rdAddr ctrlStack = (rdAddr-1, Nothing					, ctrlStack		)
ctrl CondSkip	0 pc rdAddr ctrlStack = (rdAddr  , Nothing					, succ (succ pc))
ctrl CondSkip	c pc rdAddr ctrlStack = (rdAddr  , Nothing					, succ pc		)
ctrl (Call f)	_ pc rdAddr ctrlStack = (rdAddr+1, Just (rdAddr+1, succ pc)	, f				)

stackPusher :: StAction -> Word32 -> Word8 -> (Word8, Maybe (Word8, Word32))
stackPusher Push aluOut stackPtr = (stackPtr+1, Just (stackPtr+1, aluOut))
stackPusher SNop aluOut stackPtr = (stackPtr, Nothing)
stackPusher (PushAfterPop x) aluOut stackPtr = (stackPtr-x+1, Just (stackPtr-x+1, aluOut))


topEntity = system

system :: Signal Bool -> Signal (Label, Word32, Word8)
system _ = bundle (pc, z, rdAddrC) where
	ctrlStack = asyncRam d50 rdAddrC wrDataC'
--	ctrlStack = readNew  (blockRam (replicate d50 I0)) rdAddrC' wrDataC'
	(rdAddrC', wrDataC', pc') = unbundle $ ctrl <$> cmd <*> z <*> pc <*> rdAddrC <*> ctrlStack
	rdAddrC = register 0 rdAddrC'
	pc = register def pc'

	z = alu <$> op <*> a <*> b

	ds0 = asyncRam d200 rdAddr0 wrData
	ds1 = asyncRam d200 rdAddr1 wrData

	rdAddr0 = agu <$> stackPtr <*> ia
	rdAddr1 = agu <$> stackPtr <*> ib

	stackPtr = register 0 stackPtr'
	(stackPtr', wrData) = unbundle $ stackPusher <$> g <*> z <*> stackPtr

	a = selInput <$> ds0 <*> ia
	b = selInput <$> ds1 <*> ib

	(ia, ib, op, g, cmd) = unbundle $ microcode <$> pc


microcode :: Label -> (Input, Input, Oper, StAction, Ctrl)
microcode I0  = (I 256, I 0, Cnst, Push			  , NextPC)
microcode I1  = (I 32, I 0, Cnst , Push			  , NextPC)
microcode GCD = (S 0 , I 0, IsEq , SNop			  , CondSkip)  -- SkipOnEq (S 0) (I 0)
microcode T1  = (S 1 , I 0, Cnst , PushAfterPop 2 , Return)    -- ReturnPop
microcode E1  = (S 1 , I 0, Cnst , Push           , Call DZs)  -- PushCall (S 1) DZs
microcode CA  = (S 1 , I 0, Cnst , Push           , Call DZs)  -- PushCall (S 1) DZs
microcode CB  = (S 1 , S 0, Min  , Push           , NextPC)    -- Minimum (S 1) (S 0)
microcode N1  = (S 2 , S 1, Max  , Push           , NextPC)    -- Maximum (S 2) (S 0)
microcode N2  = (S 0 , S 1, Sub  , Push           , NextPC)    -- Subtract (S 0) (S 1)
microcode N3  = (S 2 , I 0, Cnst , Push           , NextPC)    -- Push (S 2)
microcode N4  = (S 1 , I 0, Cnst , Push           , Call GCD)  -- PushCall (S 1) GCD
microcode CC  = (S 7 , S 6, Or   , Push           , NextPC)    -- BitOr (S 7) (S 6)
microcode N5  = (S 0 , I 0, Cnst , Push           , Call CZs)  -- PushCall (S 0) CZs
microcode CD  = (S 2 , S 0, ShL  , PushAfterPop 10, Return)    -- ShiftL (S 2) (S 0)
microcode DZs = (S 0 , I 0, Cnst , Push           , Call CZs)  -- PushCall (S 0) CZs
microcode CE  = (S 1 , S 0, ShR  , PushAfterPop 2 , Return)    -- ShiftR (S 1) (S 0)
microcode CZs = (S 0 , I 0, IsOdd, SNop           , CondSkip)  -- SkipOnOdd (S 0)
microcode T2  = (I 0 , I 0, Cnst , PushAfterPop 1 , Return)    -- ReturnAlter (I 0)
microcode E2  = (S 0 , I 1, ShR  , Push           , NextPC)    -- ShiftR (S 0) (I 1)
microcode N8  = (S 0 , I 0, Cnst , Push           , Call CZs)  -- PushCall (S 0) CZs
microcode CF  = (S 0 , I 1, Plus , PushAfterPop 3 , Return)    -- Plus (S 0) (I 1)

alu :: Oper -> Word32 -> Word32 -> Word32
alu Cnst  x _ = x
alu Plus  x y = x + y
alu Sub   x y = x - y
alu Or    x y = x .|. y
alu Min   x y = min x y
alu Max   x y = max x y
alu ShR   x y = x >>> y
alu ShL   x y = x <<< y
alu IsEq  x y = if x == y then 1 else 0
alu IsOdd x _ = if odd x then 1 else 0


infixl 8 >>>
(>>>) :: (Bits a,Integral b) => a -> b -> a
x >>> s = x `shiftR` fromIntegral s
infixl 8 <<<
(<<<) :: (Bits a,Integral b) => a -> b -> a
x <<< s = x `shiftL` fromIntegral s

