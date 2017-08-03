module Tests.ManualTrans where

import Data.Bits
import Data.Word
import Debug.Trace

infixl 8 >>>
(>>>) :: (Bits a,Integral b) => a -> b -> a
x >>> s = x `shiftR` fromIntegral s
infixl 8 <<<
(<<<) :: (Bits a,Integral b) => a -> b -> a
x <<< s = x `shiftL` fromIntegral s


binGCD :: Word32 -> Word32 -> Word32       
binGCD x 0 = x
binGCD x y =
  let a = dropZeros x in
  let b = dropZeros y in
  let (s,g) = (min a b, max a b) in
  binGCD s (g - s) <<< countZeros (x .|. y)

dropZeros :: Word32 -> Word32
dropZeros i = i >>> countZeros i

countZeros :: Word32 -> Word32
countZeros n = if odd n then 0 else countZeros (n >>> 1) + 1

{-  -- *** Desugaring and flatten of expressions
binGCD :: Word32 -> Word32 -> Word32
binGCD x y = 
  if (y == 0) then x
  else
    let a = dropZeros x in
    let b = dropZeros y in
    let g = max a b in
    let s = min a b in
    let d = g - s in
    let r = binGCD s d in
    let o = x .|. y in
    let e = countZeros o in
    r <<< e

dropZeros :: Word32 -> Word32
dropZeros i = 
  let s = countZeros i in
  i >>> s

countZeros :: Word32 -> Word32
countZeros n = if odd n 
  then 0 
  else
    let m = n >>> 1 in
    let c = countZeros m in
    c + 1
-}

{-  -- *** Conversion to continuation passing style

cont x f = f $! x

binGCD x y k = if (y == 0)
  then cont x k
  else
    dropZeros x
      (\a -> dropZeros y
        (\b -> cont (max a b)
          (\g -> cont (min a b)
            (\s -> cont (g - s)
              (\d -> binGCD s d
                (\r -> cont (x .|. y)
                  (\o -> countZeros o
                    (\e -> cont (r <<< e) k))))))))

dropZeros i k = 
  countZeros i
    (\s -> cont (i >>> s) k)

countZeros n k = if odd n 
  then cont 0 k
  else
    cont (n >>> 1)
      (\m -> countZeros m 
        (\c -> cont (c + 1) k))
-}

{- -- *** Defunctionalising the continuations

data Cont
  = CA Word32 Word32                                                  Cont
  | CB Word32 Word32 Word32                                           Cont
  | CC Word32 Word32 Word32 Word32                                    Cont
  | CD Word32 Word32 Word32 Word32 Word32                             Cont
  | CE Word32 Word32 Word32 Word32 Word32 Word32                      Cont
  | CF Word32 Word32 Word32 Word32 Word32 Word32 Word32               Cont
  | CG Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32        Cont
  | CH Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Cont
  | CI Word32                                                         Cont
  | CJ Word32                                                         Cont
  | CK Word32 Word32                                                  Cont
  | CNil

runBinGCD x y = binGCD x y CNil

binGCD x y                   k = if (y == 0)
                             then cont x         k
                             else dropZeros x    (CA x y               k)
dropZeros i                  k  = countZeros i   (CI i                 k)

countZeros n                 k  = if odd n
                             then cont 0         k
                             else cont (n >>> 1) (CJ n                 k)

cont a (CA x y               k) = dropZeros y    (CB x y a             k)
cont b (CB x y a             k) = cont (max a b) (CC x y a b           k)
cont g (CC x y a b           k) = cont (min a b) (CD x y a b g         k)
cont s (CD x y a b g         k) = cont (g - s)   (CE x y a b g s       k)
cont d (CE x y a b g s       k) = binGCD s d     (CF x y a b g s d     k)
cont r (CF x y a b g s d     k) = cont (x .|. y) (CG x y a b g s d r   k)
cont o (CG x y a b g s d r   k) = countZeros o   (CH x y a b g s d r o k)
cont e (CH x y a b g s d r o k) = cont (r <<< e) k
cont s (CI i                 k) = cont (i >>> s) k
cont m (CJ n                 k) = countZeros m   (CK n m               k)
cont c (CK n m               k) = cont (c + 1)   k
cont x (CNil                  ) = x
-}

{-  -- *** Translation into stack based step function
data Call = GCD Word32 Word32 | DropZs Word32 | CntZs Word32 | Cont Word32

data Context
  = CA Word32 Word32
  | CB Word32 Word32 Word32
  | CC Word32 Word32 Word32 Word32
  | CD Word32 Word32 Word32 Word32 Word32
  | CE Word32 Word32 Word32 Word32 Word32 Word32
  | CF Word32 Word32 Word32 Word32 Word32 Word32 Word32
  | CG Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32
  | CH Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32
  | CI Word32
  | CJ Word32
  | CK Word32 Word32

type Stack  = [Context]

step :: Call -> Stack -> (Call, Stack)
step (GCD x y)  cs                          = if y == 0
                                         then (Cont x        , cs                       )
                                         else (DropZs x      , CA x y               : cs)
step (Cont a)   (CA x y               : cs) = (DropZs y      , CB x y a             : cs)
step (Cont b)   (CB x y a             : cs) = (Cont (max a b), CC x y a b           : cs)
step (Cont g)   (CC x y a b           : cs) = (Cont (min a b), CD x y a b g         : cs)
step (Cont s)   (CD x y a b g         : cs) = (Cont (g - s)  , CE x y a b g s       : cs)
step (Cont d)   (CE x y a b g s       : cs) = (GCD s d       , CF x y a b g s d     : cs)
step (Cont r)   (CF x y a b s g d     : cs) = (Cont (x .|. y), CG x y a b s g d r   : cs)
step (Cont o)   (CG x y a b s g d r   : cs) = (CntZs o       , CH x y a b s g d r o : cs)
step (Cont e)   (CH x y a b s g d r o : cs) = (Cont (r <<< e), cs                       )
step (DropZs i) cs                          = (CntZs i       , CI i                 : cs)
step (Cont s)   (CI i                 : cs) = (Cont (i >>> s), cs                       )
step (CntZs n)  cs                          = if odd n
                                         then (Cont 0        , cs                       )
                                         else (Cont (n >>> 1), CJ n                 : cs)
step (Cont m)   (CJ n                 : cs) = (CntZs m       , CK n m               : cs)
step (Cont c)   (CK n m               : cs) = (Cont (c + 1)  , cs                       )

sim :: Call -> Stack -> Word32
sim (Cont x) [] = x
sim s        cs = let (s' ,cs') = step s cs in sim s' cs'
-}

{- -- *** Splitting the stack into control and data stack
data State = BinGCD | DropZs | CntZs | Cont
data Context = CA | CB | CC | CD | CE | CF | CG | CH | CI | CJ | CK
type ControlStack  = [Context]
type DataStack = [Word32]
step ::  State -> ControlStack -> DataStack -> (State, ControlStack, DataStack)
step BinGCD cs                (y:x:ds) = if y == 0
                                    then (Cont  , cs   ,             x:ds)
                                    else (DropZs, CA:cs,         x:y:x:ds)
step Cont   (CA:cs)         (a:y:x:ds) = (DropZs, CB:cs,       y:a:y:x:ds)
step Cont   (CB:cs)       (b:a:y:x:ds) = (Cont  , CC:cs,     g:b:a:y:x:ds) where g = max a b
step Cont   (CC:cs)     (g:b:a:y:x:ds) = (Cont  , CD:cs,   s:g:b:a:y:x:ds) where s = min a b
step Cont   (CD:cs)   (s:g:b:a:y:x:ds) = (Cont  , CE:cs, d:s:g:b:a:y:x:ds) where d = g - s
step Cont   (CE:cs) (d:s:g:b:a:y:x:ds) = (BinGCD, CF:cs, d:s:g:b:a:y:x:ds)
step Cont   (CF:cs)   (r:g:b:a:y:x:ds) = (Cont  , CG:cs, o:r:g:b:a:y:x:ds) where o = x .|. y
step Cont   (CG:cs) (o:r:g:b:a:y:x:ds) = (CntZs , CH:cs, o:r:g:b:a:y:x:ds)
step Cont   (CH:cs) (e:r:g:b:a:y:x:ds) = (Cont  , cs   ,             l:ds) where l = r <<< e
step DropZs cs                  (i:ds) = (CntZs , CI:cs,           i:i:ds)
step Cont   (CI:cs)           (s:i:ds) = (Cont  , cs   ,             r:ds) where r = i >>> s
step CntZs  cs                  (n:ds) = if odd n
                                    then (Cont  , cs   ,             0:ds)
                                    else (Cont  , CJ:cs,           m:n:ds) where m = n >>> 1
step Cont   (CJ:cs)           (m:n:ds) = (CntZs , CK:cs,           m:n:ds)
step Cont   (CK:cs)           (c:n:ds) = (Cont  , cs   ,             p:ds) where p = c + 1

sim :: DataStack -> State -> ControlStack -> Word32
sim ds Cont [] = head ds
sim ds s    cs = let (s', cs' ,ds') = step s cs ds in sim ds' s' cs'
-}

{- -- *** Optimizing control
data Label = BinGCD | T1 | E1 | CA | CB | CC | CDE | CFG | CH | DropZs | CI | CntZs | T2 | E2 | CK | Halt deriving Enum
type ControlStack  = [Label]
type DataStack = [Word32]
type ControlFun = Label -> ControlStack -> (Label, ControlStack)
call f pc cs = (f, succ pc : cs)
ret _ []     = (Halt, [])
ret _ (c:cs) = (c, cs)
next pc cs   = (succ pc, cs)
jump f _ cs = (f, cs)
branch e True pc cs = (succ pc, cs)
branch e False pc cs = (e, cs)

step ::  Label -> DataStack -> (ControlFun, DataStack)
step BinGCD           (y:x:ds) = (branch E1 z,           y:x:ds) where z = y == 0
step T1               (y:x:ds) = (ret        ,             x:ds)
step E1               (y:x:ds) = (call DropZs,         x:y:x:ds)
step CA             (a:y:x:ds) = (call DropZs,       y:a:y:x:ds)
step CB           (b:a:y:x:ds) = (next       ,     g:b:a:y:x:ds) where g = max a b
step CC         (g:b:a:y:x:ds) = (next       ,   s:g:b:a:y:x:ds) where s = min a b
step CDE      (s:g:b:a:y:x:ds) = (call BinGCD, d:s:g:b:a:y:x:ds) where d = g - s          -- note fused step CD/CE
step CFG      (r:g:b:a:y:x:ds) = (call CntZs , o:r:g:b:a:y:x:ds) where o = x .|. y        -- note fused step CF/CG
step CH     (e:r:g:b:a:y:x:ds) = (ret        ,             l:ds) where l = r <<< e
step DropZs             (i:ds) = (call CntZs ,           i:i:ds)
step CI               (s:i:ds) = (ret        ,             r:ds) where r = i >>> s
step CntZs              (n:ds) = (branch E2 o,             n:ds) where o = odd n
step T2                 (n:ds) = (ret        ,             z:ds) where z = 0
step E2                 (n:ds) = (call CntZs ,           m:n:ds) where m = n >>> 1        -- note fused with CJ
step CK               (c:n:ds) = (ret        ,             p:ds) where p = c + 1

sim :: DataStack -> Label -> ControlStack -> Word32
sim ds Halt [] = head ds
sim ds pc   cs = sim ds' pc' cs' where
   (cf ,ds') = step pc ds
   (pc', cs') = cf pc cs
-}

{- -- *** Splitting into separate components
data Label = BinGCD | T1 | E1 | CA | CB | CC | CDE | CFG | CH | DropZs | CI | CntZs | T2 | E2 | CK | Halt deriving (Enum, Show)
type ControlStack  = [Label]
type DataStack = [Word32]
type ControlFun = Word32 -> Label -> ControlStack -> (Label, ControlStack)
type Input = DataStack -> Word32
type AluOp = Word32 -> Word32 -> Word32
type StackMod = Word32 -> DataStack -> DataStack
call f _ pc cs = (f, succ pc : cs)
ret _ _ []     = (Halt, [])
ret _ _ (c:cs) = (c, cs)
next _ pc cs   = (succ pc, cs)
jump f _ _ cs = (f, cs)
branch e 1 pc cs = (succ pc, cs)
branch e 0 pc cs = (e, cs)
peek i ds = ds!!i
pass = const
isEq x y = if x == y then 1 else 0
isOdd x _ = if odd x then 1 else 0
keep _ ds = ds
push x ds = x : ds
popNPush n x ds = x : drop n ds
lit = const

step ::  Label -> (ControlFun, Input, Input, AluOp, StackMod)
step BinGCD = (branch E1  , peek 0, lit 0 , isEq , keep)
step T1     = (ret        , peek 1, lit 0 , pass , popNPush 2)
step E1     = (call DropZs, peek 1, lit 0 , pass , push)
step CA     = (call DropZs, peek 1, lit 0 , pass , push)
step CB     = (next       , peek 1, peek 0, max  , push)
step CC     = (next       , peek 2, peek 1, min  , push)
step CDE    = (call BinGCD, peek 1, peek 0, (-)  , push)
step CFG    = (call CntZs , peek 5, peek 4, (.|.), push)
step CH     = (ret        , peek 1, peek 0, (<<<), popNPush 7)
step DropZs = (call CntZs , peek 0, lit 0 , pass , push)
step CI     = (ret        , peek 1, peek 0, (>>>), popNPush 2)
step CntZs  = (branch E2  , peek 0, lit 0 , isOdd, keep)
step T2     = (ret        , lit 0 , lit 0 , pass , popNPush 1)
step E2     = (call CntZs , peek 0, lit 1 , (>>>), push)
step CK     = (ret        , peek 0, lit 1 , (+)  , popNPush 2)

sim :: DataStack -> Label -> ControlStack -> Word32
sim ds Halt [] = head ds
sim ds pc   cs = {- trace (show pc ++ " " ++ show (x,y) ++ " " ++ show z ++ "   " ++ show cs' ++ "    " ++ show ds) $ -} sim ds' pc' cs' where
   (cf, ia, ib, oper, sm) = step pc
   x = ia ds
   y = ib ds
   z = oper x y
   ds' = sm z ds
   (pc', cs') = cf z pc cs
-}

{- -} -- *** introduce encoding for each component
data Label = BinGCD | T1 | E1 | CA | CB | CC | CDE | CFG | CH | DropZs | CI | CntZs | T2 | E2 | CK | Halt deriving (Enum, Show)
type DataStack = [Word32]
type CtrlStack = [Label]
data Input = S Int | I Word32
data AluOp = Pass | Add | Sub | Or | Min | Max | ShR | ShL | IsEq | IsOdd deriving Show
data StAction = Keep | Push | PopNPush Int
data Ctrl = Next | Return | Branch Label | Call Label

microcode ::  Label -> (Ctrl, Input, Input, AluOp, StAction)
microcode BinGCD = (Branch E1  , S 0, I 0, IsEq , Keep)
microcode T1     = (Return     , S 1, I 0, Pass, PopNPush 2)
microcode E1     = (Call DropZs, S 1, I 0, Pass, Push)
microcode CA     = (Call DropZs, S 1, I 0, Pass, Push)
microcode CB     = (Next       , S 1, S 0, Max  , Push)
microcode CC     = (Next       , S 2, S 1, Min  , Push)
microcode CDE    = (Call BinGCD, S 1, S 0, Sub  , Push)
microcode CFG    = (Call CntZs , S 5, S 4, Or   , Push)
microcode CH     = (Return     , S 1, S 0, ShL  , PopNPush 7)
microcode DropZs = (Call CntZs , S 0, I 0, Pass, Push)
microcode CI     = (Return     , S 1, S 0, ShR  , PopNPush 2)
microcode CntZs  = (Branch E2  , S 0, I 0, IsOdd, Keep)
microcode T2     = (Return     , I 0, I 0, Pass, PopNPush 1)
microcode E2     = (Call CntZs , S 0, I 1, ShR  , Push)
microcode CK     = (Return     , S 0, I 1, Add  , PopNPush 2)

alu :: AluOp -> Word32 -> Word32 -> Word32
alu Pass  x _ = x
alu Add   x y = x + y
alu Sub   x y = x - y
alu Or    x y = x .|. y
alu Min   x y = min x y
alu Max   x y = max x y
alu ShR   x y = x >>> y
alu ShL   x y = x <<< y
alu IsEq  x y = if x == y then 1 else 0
alu IsOdd x _ = if odd x then 1 else 0

selInput :: DataStack -> Input -> Word32
selInput ds (S i) = ds !! i
selInput _  (I x) = x

stackMod :: StAction -> Word32 -> DataStack -> DataStack
stackMod Keep         _ ds = ds
stackMod Push         x ds = x : ds
stackMod (PopNPush n) x ds = x : drop n ds

ctrl :: Ctrl -> Word32 -> Label -> [Label] -> (Label, [Label])
ctrl Next       _ pc cs = (succ pc, cs)
ctrl (Branch e) 1 pc cs = (succ pc, cs)
ctrl (Branch e) 0 pc cs = (e, cs)
ctrl (Call f  ) _ pc cs = (f, succ pc : cs)
ctrl Return  _ _ []     = (Halt, [])
ctrl Return  _ _ (c:cs) = (c, cs)

sim :: DataStack -> Label -> [Label] -> Word32
sim ds Halt _  = head ds
sim ds pc   cs = {-trace (show pc ++ " " ++ show op ++ " " ++ show (x,y) ++ " " ++ show z ++ "   " ++ show cs' ++ "    " ++ show ds) $ -}sim ds' pc' cs' where
  (f, ia, ib, op, g) = microcode pc
  x = selInput ds ia
  y = selInput ds ib
  z = alu op x y 
  ds' = stackMod g z ds
  (pc',cs') = ctrl f z pc cs
