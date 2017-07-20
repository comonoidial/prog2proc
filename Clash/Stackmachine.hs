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

inputMux :: Input -> Word32 -> Word32
inputMux (S _) a = a
inputMux (I x) _ = x

agu :: Word8 -> Input -> Word8
agu stackSp (S i) = stackSp - i
agu stackSp (I _) = stackSp

ctrl :: Ctrl -> Word32 -> Label -> Word8 -> Label -> (Word8, Maybe (Word8, Label), Label)
ctrl Next       _ nPC cSP retPC = (cSP  , Nothing          , nPC)
ctrl Return     _ nPC cSP retPC = (cSP-1, Nothing          , retPC)
ctrl (Branch e) 0 nPC cSP retPC = (cSP  , Nothing          , e)
ctrl (Branch e) _ nPC cSP retPC = (cSP  , Nothing          , nPC)
ctrl (Call f)   _ nPC cSP retPC = (cSP+1, Just (cSP+1, nPC), f)

stackMod :: StAction -> Word32 -> Word8 -> (Word8, Maybe (Word8, Word32))
stackMod Keep         dSP z = (dSP , Nothing)
stackMod Push         dSP z = (dSP', Just (dSP', z)) where dSP' = dSP+1
stackMod (PopNPush n) dSP z = (dSP', Just (dSP', z)) where dSP' = dSP-n+1

topEntity = proccesor

proccesor :: Signal () -> Signal (Label, Word32)
proccesor _ = bundle (pc, z) where
  pc = register def pc'
  (ctrlOp, ia, ib, oper, stOp) = liftB microcode pc

   nPC = liftA succ pc
  (cSP', savePC, pc') = liftB5 ctrl ctrlOp z nPC cSP retPC
  cSP = register 0 cSP'
  retPC = asyncRam d64 cSP savePC

  rdA = liftA2 agu dSP ia
  rdB = liftA2 agu dSP ib
  a = asyncRam d128 rdA wrData
  b = asyncRam d128 rdB wrData

  x = liftA2 inputMux ia ds0
  y = liftA2 inputMux id ds1
  z = liftA3 alu oper x y

  dSP = register 0 dSP'
  (dSP', wrData) = liftB3 stackMod stOp dSP z

microcode :: Label -> (Ctrl, Input, Input, Oper, StAction)
microcode I0     = (Next      ,I 256, I 0, Const, Push)
microcode I1     = (Next       ,I 32, I 0, Const, Push)
microcode BinGCD = (Branch E1  , S 0, I 0, IsEq , Keep)
microcode T1     = (Return     , S 1, I 0, Const, PopNPush 2)
microcode E1     = (Call DropZs, S 1, I 0, Const, Push)
microcode CA     = (Call DropZs, S 1, I 0, Const, Push)
microcode CB     = (Next       , S 1, S 0, Max  , Push)
microcode CC     = (Next       , S 2, S 1, Min  , Push)
microcode CDE    = (Call BinGCD, S 1, S 0, Sub  , Push)
microcode CFG    = (Call CntZs , S 5, S 4, Or   , Push)
microcode CH     = (Return     , S 1, S 0, ShL  , PopNPush 7)
microcode DropZs = (Call CntZs , S 0, I 0, Const, Push)
microcode CI     = (Return     , S 1, S 0, ShR  , PopNPush 2)
microcode CntZs  = (Branch E2  , S 0, I 0, IsOdd, Keep)
microcode T2     = (Return     , I 0, I 0, Const, PopNPush 1)
microcode E2     = (Call CntZs , S 0, I 1, ShR  , Push)
microcode CK     = (Return     , S 0, I 1, Add  , PopNPush 2)

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

liftB = unbundle . liftA
liftB2 = unbundle . liftA2
liftB3 = unbundle . liftA3

liftA5 f p q r s t = f <$> p <*> q <*> r <*> s <*> t
liftB5 = unbundle . liftA5
