module StackMachine where
import CLaSH.Prelude
import Data.Bits
import Data.Word
import Debug.Trace

data Label = I0 | I1 | BinGCD | T1 | E1 | CA | CB | CC | CDE | CFG | CH | DropZs | CI | CntZs | T2 | E2 | CK deriving (Enum, Show)

instance Default Label where
	def = I0

data Ctrl = Next | Return | Branch Label | Call Label
data Oper = Const  | Plus | Sub | Or | Min | Max | ShR | ShL | IsEq | IsOdd deriving Show
data Input = S Word8 | I Word32
data StAction = SNop | Push | PushAfterPop Word8

selInput :: Word32 -> Input -> Word32
selInput a (S _) = a
selInput _ (I x) = x

agu :: Word8 -> Input -> Word8
agu stackSp (S i) = stackSp - i
agu stackSp (I _) = stackSp

ctrl :: Ctrl -> Word32 -> Label -> Word8 -> Label -> (Word8, Maybe (Word8, Label), Label)
ctrl Next		_ pc rdAddr ctrlStack = (rdAddr  , Nothing					, succ pc	)
ctrl Return		_ pc rdAddr ctrlStack = (rdAddr-1, Nothing					, ctrlStack	)
ctrl (Branch e)	0 pc rdAddr ctrlStack = (rdAddr  , Nothing					, e			)
ctrl (Branch e)	c pc rdAddr ctrlStack = (rdAddr  , Nothing					, succ pc	)
ctrl (Call f)	_ pc rdAddr ctrlStack = (rdAddr+1, Just (rdAddr+1, succ pc)	, f			)

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

	(cmd, ia, ib, op, g) = unbundle $ microcode <$> pc


microcode :: Label -> (Ctrl, Input, Input, Oper, StAction)
microcode I0     = (Next      ,I 256, I 0, Const, Push)
microcode I1     = (Next       ,I 32, I 0, Const, Push)
microcode BinGCD = (Branch E1  , S 0, I 0, IsEq , Keep)
microcode T1     = (Return     , S 1, I 0, Const, PushAfterPop 2)
microcode E1     = (Call DropZs, S 1, I 0, Const, Push)
microcode CA     = (Call DropZs, S 1, I 0, Const, Push)
microcode CB     = (Next       , S 1, S 0, Max  , Push)
microcode CC     = (Next       , S 2, S 1, Min  , Push)
microcode CDE    = (Call BinGCD, S 1, S 0, Sub  , Push)
microcode CFG    = (Call CntZs , S 5, S 4, Or   , Push)
microcode CH     = (Return     , S 1, S 0, ShL  , PushAfterPop 7)
microcode DropZs = (Call CntZs , S 0, I 0, Const, Push)
microcode CI     = (Return     , S 1, S 0, ShR  , PushAfterPop 2)
microcode CntZs  = (Branch E2  , S 0, I 0, IsOdd, Keep)
microcode T2     = (Return     , I 0, I 0, Const, PushAfterPop 1)
microcode E2     = (Call CntZs , S 0, I 1, ShR  , Push)
microcode CK     = (Return     , S 0, I 1, Add  , PushAfterPop 2)

alu :: Oper -> Word32 -> Word32 -> Word32
alu Const x _ = x
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

