module Tests.BinGCD where

import qualified Prelude as P (lookup)
import Prelude hiding (lookup)
import Data.Bits
import Data.Word
import Debug.Trace

infixl 8 >>>
(>>>) :: (Bits a,Integral b) => a -> b -> a
x >>> s = x `shiftR` fromIntegral s
infixl 8 <<<
(<<<) :: (Bits a,Integral b) => a -> b -> a
x <<< s = x `shiftL` fromIntegral s

nop = id
pop (x:xs) = xs
push x xs = (x:xs)
alter x (y:ys) = (x:ys)
top (x:xs) = x
keep x = x

binGCD :: Word32 -> Word32 -> Word32       
binGCD u 0 = u
binGCD u v =
  let a = dropZeros u in
  let b = dropZeros v in
  let x = min a b in
  let y = max a b in
  binGCD x (y - x) <<< countZeros (u .|. v)

dropZeros :: Word32 -> Word32
dropZeros x = x >>> countZeros x

countZeros :: Word32 -> Int
countZeros x = if odd x then 0 else countZeros (x >>> 1) + 1

{- -- *** Introducing names for all recursive calls
binGCD :: Word32 -> Word32 -> Word32       
binGCD u 0 = u
binGCD u v =
  let a = dropZeros u in
  let b = dropZeros v in
  let x = min a b in
  let y = max a b in
  let g = binGCD x (y - x) in
  let e = countZeros (u .|. v) in
  g <<< e

dropZeros :: Word32 -> Word32
dropZeros x = 
  let s = countZeros x in
  x >>> s

countZeros :: Word32 -> Int
countZeros x = if odd x then 0 
  else 
  let c = countZeros (x >>> 1) in
  c + 1
-}

{- -- *** Translation into stack based step function
type StackAction = [Context] -> [Context]
data State = BinGCD Word32 Word32 | DropZeros Word32 | CountZeros Word32 | R Word32 | R' Int
data Context = CA Word32 Word32 | CB Word32 Word32 Word32 | CC Word32 Word32 Word32 Word32  | CD Word32 Word32 Word32 Word32 Word32 | CE Word32 | CF Word32
step :: State -> Context -> (State, StackAction)
step (BinGCD u v) _        = if v == 0 
                        then (R u                 , nop)
                        else (DropZeros u         , push (CA u v))
step (R a) (CA u v)        = (DropZeros v         , alter (CB u v a))
step (R b) (CB u v a)      = let x = min a b in
                             let y = max a b in
                             (BinGCD x (y - x)    , alter (CC u v a b))
step (R g) (CC u v a b)    = (CountZeros (u .|. v), alter (CD u v a b g))
step (R' e) (CD u v a b g) = (R (g <<< e)         , pop)
step (DropZeros x) _       = (CountZeros x        , push (CE x))
step (R' s) (CE x)         = (R (x >>> s)         , pop)
step (CountZeros x) _      = if odd x
                        then (R' 0, nop)
                        else (CountZeros (x >>> 1), push (CF x))
step (R' c) (CF x)         = (R' (c + 1)          , pop)

sim :: State -> [Context] -> Word32
sim (R x) []   = x
sim s     []   = let (s' ,f) = step s undefined in sim s' (f [])
sim s cs@(c:_) = let (s' ,f) = step s c in sim s' (f cs)
-}

{-  -- *** Introducing names for all non trival expression
binGCD :: Word32 -> Word32 -> Word32       
binGCD u 0 = u
binGCD u v =
  let a = dropZeros u in
  let b = dropZeros v in
  let x = min a b in
  let y = max a b in
  let z = y - x in
  let g = binGCD x z in
  let o = u .|. v in
  let e = countZeros o in
  g <<< e

dropZeros :: Word32 -> Word32
dropZeros x = 
  let s = countZeros x in
  x >>> s

countZeros :: Word32 -> Int
countZeros x =
  let o = odd x in
  if o 
    then 0 
    else
    let y = x >>> 1 in
    let c = countZeros y in
    c + 1
-}

{-  -- *** Translation into stack based step function
type StackAction = [Context] -> [Context]
data State = GCD Word32 Word32 | DropZs Word32 | CountZs Word32 | R Word32 | R' Int | N1 Word32 Word32 Word32 Word32 Word32 | N2 Word32 Word32 Word32 Word32 Word32 Word32 
  | N3 Word32 Word32 Word32 Word32 Word32 Word32 Word32 | N4 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 | N5 Word32  Word32
data Context = CA Word32 Word32 | CB Word32 Word32 Word32 | CC Word32 Word32 Word32 Word32 Word32 Word32 Word32 | CD Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 | CE Word32 | CF Word32 Word32
step :: State -> Context -> (State, StackAction)
step (GCD u v) _              = if v == 0
                           then (R u                   , keep)
                           else (DropZs u              , push (CA u v))
step (R a) (CA u v)           = (DropZs v              , alter (CB u v a))
step (R b) (CB u v a)         = (N1 u v a b (min a b)  , pop)
step (N1 u v a b x) _         = (N2 u v a b x (max a b), keep)
step (N2 u v a b x y) _       = (N3 u v a b x y (y - x), keep)
step (N3 u v a b x y z) _     = (BinGCD x z            , push (CC u v a b x y z))
step (R g) (CC u v a b x y z) = (N4 u v a b x y z g (u .|. v), pop)
step (N4 u v a b x y z g o) _ = (CountZs o, push (CD u v a b x y z g o))
step (R' e) (CD u v a b x y z g o) = (R (g <<< e)      , pop)
step (DropZs x) _             = (CountZs x             , push (CE x))
step (R' s) (CE x)            = (R (x >>> s)           , pop)
step (CountZs x) _            = if odd x
                           then (R' 0                  , keep)
                           else (N5 x (x >>> 1)        , keep)
step (N5 x   y) _             = (CountZs y             , push (CF x y))
step (R' c) (CF x y)          = (R' (c + 1)            , pop)

sim :: State -> [Context] -> Word32
sim (R x) []   = x
sim s     []   = let (s' ,f) = step s undefined in sim s' (f [])
sim s cs@(c:_) = let (s' ,f) = step s c in sim s' (f cs)
-}

{- -- *** Introducing data stack to avoid copying around many values from state to context and back
(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! n

type StackAction a = [a] -> [a]
data State = GCD | DropZs | CntZs | Ret | N1 | N2 | N3 | N4 | N5 | N6 | N7 | N8 | N9
data Context = CA | CB | CC | CD | CE | CF
type DataStack = [Word32]
step :: DataStack -> State -> Context -> (StackAction Word32, State, StackAction Context)
step ds GCD _  = if ds#0 == 0
            then (pop                     , Ret   , keep)
            else (push (ds#1)             , DropZs, push CA)
step ds Ret CA = (push (ds#1)             , DropZs, alter CB)
step ds Ret CB = (push (min (ds#1) (ds#0)), N1    , pop)     
step ds N1  _  = (push (max (ds#2) (ds#1)), N2    , keep)
step ds N2  _  = (push ((ds#0) - (ds#1))  , N3    , keep)
step ds N3  _  = (push (ds#2)             , N4    , keep)
step ds N4  _  = (push (ds#1)             , GCD   , push CC)
step ds Ret CC = (push ((ds#7) .|. (ds#6)), N5    , pop)
step ds N5  _  = (push (ds#0)             , CntZs , push CD)
step ds Ret CD = (push ((ds#2) <<< (ds#0)), N6    , pop)
step ds N6  _  = (popSndN 10              , Ret   , keep)
step ds DropZs _ = (push (ds#0), CntZs, push CE)
step ds Ret CE = (push ((ds#1) >>> (ds#0)), N7    , pop)
step ds N7  _  = (popSndN 2               , Ret   , keep)
step ds CntZs _ = if odd (ds#0)
            then (alter 0                 , Ret   , keep)
            else (push ((ds#0) >>> 1)     , N8    , keep)
step ds N8  _  = (push (ds#0)             , CntZs , push CF)
step ds Ret CF = (push ((ds#0) + 1)       , N9    , pop)
step ds N9  _  = (popSndN 3               , Ret   , keep)

sim :: DataStack -> State -> [Context] -> Word32
sim ds Ret   []   = top ds
sim ds s     []   = let (g , s' ,f) = step ds s undefined in sim (g ds) s' (f [])
sim ds s cs@(c:_) = let (g , s' ,f) = step ds s c         in sim (g ds) s' (f cs)
-}

{- -- *** Merge Context stack and State into a control stack with labels

(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! n
call f c (x:xs) = f:c:xs
returning = pop
nextTo x = alter x

type StackAction a = [a] -> [a]
data Label = GCD | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DropZs | CE | N7 | CntZs | N8 | CF | N9
type DataStack = [Word32]
step :: DataStack -> Label -> (StackAction Word32, StackAction Label)
step ds GCD = if ds#0 == 0
         then (pop                     , returning)
         else (push (ds#1)             , call DropZs CA)
step ds CA  = (push (ds#1)             , call DropZs CB)
step ds CB  = (push (min (ds#1) (ds#0)), nextTo N1)     
step ds N1  = (push (max (ds#2) (ds#1)), nextTo N2)
step ds N2  = (push ((ds#0) - (ds#1))  , nextTo N3)
step ds N3  = (push (ds#2)             , nextTo N4)
step ds N4  = (push (ds#1)             , call GCD CC)
step ds CC  = (push ((ds#7) .|. (ds#6)), nextTo N5)
step ds N5  = (push (ds#0)             , call CntZs CD)
step ds CD  = (push ((ds#2) <<< (ds#0)), nextTo N6)
step ds N6  = (popSndN 10              , returning)
step ds DropZs = (push (ds#0)          , call CntZs CE)
step ds CE  = (push ((ds#1) >>> (ds#0)), nextTo N7)
step ds N7  = (popSndN 2               , returning)
step ds CntZs = if odd (ds#0)
         then (alter 0                 , returning)
         else (push ((ds#0) >>> 1)     , nextTo N8)
step ds N8  = (push (ds#0)             , call CntZs CF)
step ds CF  = (push ((ds#0) + 1)       , nextTo N9)
step ds N9  = (popSndN 3               , returning)

sim :: DataStack -> [Label] -> Word32
sim ds []       = top ds
sim ds cs@(c:_) = let (g, f) = step ds c in sim (g ds) (f cs)
-}

{- -- *** Labels into program counter and conditional branching

(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! n
call f (x:xs) = f:(succ x):xs
returning = pop
nextPC (x:xs) = succ x : xs
equals x  y = x == y
condSkip True  (x:xs) = succ x : xs
condSkip False (x:xs) = succ (succ x) : xs

type StackAction a = [a] -> [a]
data Label = GCD | T1 | E1 | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DropZs | CE | N7 | CntZs | T2 | E2 | N8 | CF | N9 deriving Enum
type DataStack = [Word32]
step :: DataStack -> Label -> (StackAction Word32, StackAction Label)
step ds GCD = (keep                    , condSkip (equals (ds#0) 0))
step ds T1  = (pop                     , returning)
step ds E1  = (push (ds#1)             , call DropZs)
step ds CA  = (push (ds#1)             , call DropZs)
step ds CB  = (push (min (ds#1) (ds#0)), nextPC)     
step ds N1  = (push (max (ds#2) (ds#1)), nextPC)
step ds N2  = (push ((ds#0) - (ds#1))  , nextPC)
step ds N3  = (push (ds#2)             , nextPC)
step ds N4  = (push (ds#1)             , call GCD)
step ds CC  = (push ((ds#7) .|. (ds#6)), nextPC)
step ds N5  = (push (ds#0)             , call CntZs)
step ds CD  = (push ((ds#2) <<< (ds#0)), nextPC)
step ds N6  = (popSndN 10              , returning)
step ds DropZs = (push (ds#0)          , call CntZs)
step ds CE  = (push ((ds#1) >>> (ds#0)), nextPC)
step ds N7  = (popSndN 2               , returning)
step ds CntZs = (keep                  , condSkip (odd (ds#0)))
step ds T2  = (alter 0                 , returning)
step ds E2  = (push ((ds#0) >>> 1)     , nextPC)
step ds N8  = (push (ds#0)             , call CntZs)
step ds CF  = (push ((ds#0) + 1)       , nextPC)
step ds N9  = (popSndN 3               , returning)

sim :: DataStack -> [Label] -> Word32
sim ds []       = top ds
sim ds cs@(c:_) = let (g, f) = step ds c in sim (g ds) (f cs)
-}

{- -- *** Splitting off the arithmetic expressions

(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! (fromIntegral n)
call f _ (x:xs) = f:(succ x):xs
returning _ = pop
nextPC _ (x:xs) = succ x : xs
equals x y = if x == y then 1 else 0
isOdd x = if odd x then 1 else 0
condSkip 0 (x:xs) = succ (succ x) : xs
condSkip _ (x:xs) = succ x : xs
keep' _ = keep
pop' _ = pop

type StackAction a = Word32 -> [a] -> [a]
data Label = GCD | T1 | E1 | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DZs | CE | N7 | CZs | T2 | E2 | N8 | CF | N9 deriving Enum
type DataStack = [Word32]
step :: DataStack -> Label -> (Word32, StackAction Word32, StackAction Label)
step ds GCD = (equals (ds#0) 0  , keep'  , condSkip)
step ds T1  = (0                , pop'   , returning)
step ds E1  = (ds#1             , push   , call DZs)
step ds CA  = (ds#1             , push   , call DZs)
step ds CB  = (min (ds#1) (ds#0), push   , nextPC)     
step ds N1  = (max (ds#2) (ds#1), push   , nextPC)
step ds N2  = ((ds#0) - (ds#1)  , push   , nextPC)
step ds N3  = (ds#2             , push   , nextPC)
step ds N4  = (ds#1             , push   , call GCD)
step ds CC  = ((ds#7) .|. (ds#6), push   , nextPC)
step ds N5  = (ds#0             , push   , call CZs)
step ds CD  = ((ds#2) <<< (ds#0), push   , nextPC)
step ds N6  = (10               , popSndN, returning)
step ds DZs = (ds#0             , push   , call CZs)
step ds CE  = ((ds#1) >>> (ds#0), push   , nextPC)
step ds N7  = (2                , popSndN, returning)
step ds CZs = (isOdd (ds#0)     , keep'  , condSkip)
step ds T2  = (0                , alter  , returning)
step ds E2  = ((ds#0) >>> 1     , push   , nextPC)
step ds N8  = (ds#0             , push   , call CZs)
step ds CF  = ((ds#0) + 1       , push   , nextPC)
step ds N9  = (3                , popSndN, returning)

sim :: DataStack -> [Label] -> Word32
sim ds []       = top ds
sim ds cs@(c:_) = let (x, g, f) = step ds c in sim (g x ds) (f x cs)
-}

{- -- *** split off argument values
(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! (fromIntegral n)
call f _ (x:xs) = f:(succ x):xs
returning _ = pop
nextPC _ (x:xs) = succ x : xs
equals x y = if x == y then 1 else 0
isOdd x _ = if odd x then 1 else 0
condSkip 0 (x:xs) = succ (succ x) : xs
condSkip _ (x:xs) = succ x : xs
keep' _ = keep
pop' _ = pop
data Input = S Int | I Word32
selInput ds (S i) = ds#i
selInput _  (I x) = x
type StackAction a = Word32 -> [a] -> [a]
data Label = GCD | T1 | E1 | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DZs | CE | N7 | CZs | T2 | E2 | N8 | CF | N9 deriving Enum
type DataStack = [Word32]
step :: DataStack -> Label -> (Word32, Word32, Word32 -> Word32 -> Word32, StackAction Word32, StackAction Label)
step ds GCD = (ds#0, 0   , equals, keep'  , condSkip)
step ds T1  = (0   , 0   , const , pop'   , returning)
step ds E1  = (ds#1, 0   , const , push   , call DZs)
step ds CA  = (ds#1, 0   , const , push   , call DZs)
step ds CB  = (ds#1, ds#0, min   , push   , nextPC)     
step ds N1  = (ds#2, ds#1, max   , push   , nextPC)
step ds N2  = (ds#0, ds#1, (-)   , push   , nextPC)
step ds N3  = (ds#2, 0   , const , push   , nextPC)
step ds N4  = (ds#1, 0   , const , push   , call GCD)
step ds CC  = (ds#7, ds#6, (.|.) , push   , nextPC)
step ds N5  = (ds#0, 0   , const , push   , call CZs)
step ds CD  = (ds#2, ds#0, (<<<) , push   , nextPC)
step ds N6  = (10  , 0   , const , popSndN, returning)
step ds DZs = (ds#0, 0   , const , push   , call CZs)
step ds CE  = (ds#1, ds#0, (>>>) , push   , nextPC)
step ds N7  = (2   , 0   , const , popSndN, returning)
step ds CZs = (ds#0, 0   , isOdd , keep'  , condSkip)
step ds T2  = (0   , 0   , const , alter  , returning)
step ds E2  = (ds#0, 1   , (>>>) , push   , nextPC)
step ds N8  = (ds#0, 0   , const , push   , call CZs)
step ds CF  = (ds#0, 1   , (+)   , push   , nextPC)
step ds N9  = (3   , 0   , const , popSndN, returning)

sim :: DataStack -> [Label] -> Word32
sim ds []       = top ds
sim ds cs@(c:_) = let (a, b, o, g, f) = step ds c in let x = o a b in sim (g x ds) (f x cs)
-}

{- -} -- *** introduce encoding for each component
(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! (fromIntegral n)
call f (x:xs) = f:(succ x):xs
nextPC (x:xs) = succ x : xs
condSkip 0 (x:xs) = succ (succ x) : xs
condSkip _ (x:xs) = succ x : xs
data Input = S Int | I Word32
selInput ds (S i) = ds#i
selInput _  (I x) = x

data Label = GCD | T1 | E1 | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DZs | CE | N7 | CZs | T2 | E2 | N8 | CF | N9 deriving (Enum,Show)
type DataStack = [Word32]
type CtrlStack = [Label]
data Oper = Const | Plus | Sub | Or | Min | Max | ShR | ShL | IsEq | IsOdd deriving Show
data StAction = Keep | Pop | Push | Alter | PopSN
data Ctrl = NextPC | Return | CondSkip | Call Label

lookup :: Label -> (Input, Input, Oper, StAction, Ctrl)
lookup GCD = (S 0 , I 0, IsEq , Keep , CondSkip)  -- SkipOnEq (S 0) (I 0)
lookup T1  = (I 0 , I 0, Const, Pop  , Return)    -- ReturnPop
lookup E1  = (S 1 , I 0, Const, Push , Call DZs)  -- PushCall (S 1) DZs
lookup CA  = (S 1 , I 0, Const, Push , Call DZs)  -- PushCall (S 1) DZs
lookup CB  = (S 1 , S 0, Min  , Push , NextPC)    -- Minimum (S 1) (S 0)
lookup N1  = (S 2 , S 1, Max  , Push , NextPC)    -- Maximum (S 2) (S 0)
lookup N2  = (S 0 , S 1, Sub  , Push , NextPC)    -- Subtract (S 0) (S 1)
lookup N3  = (S 2 , I 0, Const, Push , NextPC)    -- Push (S 2)
lookup N4  = (S 1 , I 0, Const, Push , Call GCD)  -- PushCall (S 1) GCD
lookup CC  = (S 7 , S 6, Or   , Push , NextPC)    -- BitOr (S 7) (S 6)
lookup N5  = (S 0 , I 0, Const, Push , Call CZs)  -- PushCall (S 0) CZs
lookup CD  = (S 2 , S 0, ShL  , Push , NextPC)    -- ShiftL (S 2) (S 0)
lookup N6  = (I 10, I 0, Const, PopSN, Return)    -- ReturnClear 10
lookup DZs = (S 0 , I 0, Const, Push , Call CZs)  -- PushCall (S 0) CZs
lookup CE  = (S 1 , S 0, ShR  , Push , NextPC)    -- ShiftR (S 1) (S 0)
lookup N7  = (I 2 , I 0, Const, PopSN, Return)    -- ReturnClear 2
lookup CZs = (S 0 , I 0, IsOdd, Keep , CondSkip)  -- SkipOnOdd (S 0)
lookup T2  = (I 0 , I 0, Const, Alter, Return)    -- ReturnAlter (I 0)
lookup E2  = (S 0 , I 1, ShR  , Push , NextPC)    -- ShiftR (S 0) (I 1)
lookup N8  = (S 0 , I 0, Const, Push , Call CZs)  -- PushCall (S 0) CZs
lookup CF  = (S 0 , I 1, Plus , Push , NextPC)    -- Plus (S 0) (I 1)
lookup N9  = (I 3 , I 0, Const, PopSN, Return)    -- ReturnClear 3

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

stackMod :: StAction -> Word32 -> DataStack -> DataStack
stackMod Keep  _ = keep
stackMod Pop   _ = pop
stackMod Push  x = push x
stackMod Alter x = alter x
stackMod PopSN x = popSndN x

ctrl :: Ctrl -> Word32 -> CtrlStack -> CtrlStack
ctrl NextPC   _ = nextPC
ctrl Return   _ = pop
ctrl CondSkip c = condSkip c
ctrl (Call f) _ = call f

sim :: DataStack -> [Label] -> Word32
sim ds []       = top ds
sim ds (pc:cs) = {-trace (show pc ++ " " ++ show op ++ " " ++ show (x,y) ++ " " ++ show z ++ "   " ++ show cs' ++ "    " ++ show ds) $ -}sim ds' cs' where
  (ia, ib, op, g, f) = lookup pc
  x = selInput ds ia
  y = selInput ds ib
  z = alu op x y 
  ds' = stackMod g z ds
  cs' = ctrl f z (pc:cs)
{- -}

{- -- *** splitting instruction memory and decoder
(#) :: [a] -> Int -> a
(#) = (!!)
popSnd (x:y:s) = (x:s)
popSndN n xs = iterate popSnd xs !! (fromIntegral n)
data Input = S Int | I Word32
selInput ds (S i) = ds#i
selInput _  (I x) = x

data Label = GCD | T1 | E1 | CA | CB | N1 | N2 | N3 | N4 | CC | N5 | CD | N6 | DZs | CE | N7 | CZs | T2 | E2 | N8 | CF | N9 deriving (Eq,Ord,Enum,Show)
type DataStack = [Word32]
type CtrlStack = [Label]
data Oper = Const | Add | Sub | Or | Min | Max | ShR | ShL | IsEq | IsOdd deriving Show
data StAction = Keep | Pop | Push | Alter | PopSN
data Ctrl = NextPC | Return | CondSkip | Call Label
data Instr 
  = PushVal Input  
  | PushCall Input Label
  | ReturnClear Word32
  | ReturnPop
  | ReturnAlter Input
  | Minimum Input Input
  | Maximum Input Input
  | Subtract Input Input
  | Plus Input Input
  | BitOr Input Input
  | ShiftL Input Input
  | ShiftR Input Input
  | SkipOnEq Input Input
  | SkipOnOdd Input

instrMem :: [(Label, Instr)]
instrMem =
  [(GCD, SkipOnEq (S 0) (I 0))
  ,(T1 , ReturnPop           )
  ,(E1 , PushCall (S 1) DZs  )
  ,(CA , PushCall (S 1) DZs  )
  ,(CB , Minimum (S 1) (S 0) )
  ,(N1 , Maximum (S 2) (S 1) )
  ,(N2 , Subtract (S 0) (S 1))
  ,(N3 , PushVal (S 2)       )
  ,(N4 , PushCall (S 1) GCD  )
  ,(CC , BitOr (S 7) (S 6)   )
  ,(N5 , PushCall (S 0) CZs  )
  ,(CD , ShiftL (S 2) (S 0)  )
  ,(N6 , ReturnClear 10      )
  ,(DZs, PushCall (S 0) CZs  )
  ,(CE , ShiftR (S 1) (S 0)  )
  ,(N7 , ReturnClear 2       )
  ,(CZs, SkipOnOdd (S 0)     )
  ,(T2 , ReturnAlter (I 0)   )
  ,(E2 , ShiftR (S 0) (I 1)  )
  ,(N8 , PushCall (S 0) CZs  )
  ,(CF , Plus (S 0) (I 1)    )
  ,(N9 , ReturnClear 3       )
  ]

decode :: Instr -> (Input, Input, Oper, StAction, Ctrl)
decode (PushVal x    ) = (x  , I 0, Const, Push , NextPC)
decode (PushCall x f ) = (x  , I 0, Const, Push , Call f)
decode (ReturnClear n) = (I n, I 0, Const, PopSN, Return)
decode (ReturnPop    ) = (I 0, I 0, Const, Pop  , Return)
decode (ReturnAlter x) = (x  , I 0, Const, Alter, Return)
decode (Minimum x y  ) = (x  , y  , Min  , Push , NextPC)
decode (Maximum x y  ) = (x  , y  , Max  , Push , NextPC)
decode (Subtract x y ) = (x  , y  , Sub  , Push , NextPC)
decode (Plus x y     ) = (x  , y  , Add  , Push , NextPC)
decode (BitOr x y    ) = (x  , y  , Or   , Push , NextPC)
decode (ShiftL x y   ) = (x  , y  , ShL  , Push , NextPC)
decode (ShiftR x y   ) = (x  , y  , ShR  , Push , NextPC)
decode (SkipOnEq x y ) = (x  , y  , IsEq , Keep , CondSkip)
decode (SkipOnOdd x  ) = (x  , I 0, IsOdd, Keep , CondSkip) 
  
alu :: Oper -> Word32 -> Word32 -> Word32
alu Const x _ = x
alu Add   x y = x + y
alu Sub   x y = x - y
alu Or    x y = x .|. y
alu Min   x y = min x y
alu Max   x y = max x y
alu ShR   x y = x >>> y
alu ShL   x y = x <<< y
alu IsEq  x y = if x == y then 1 else 0
alu IsOdd x _ = if odd x then 1 else 0

stackMod :: StAction -> Word32 -> DataStack -> DataStack
stackMod Keep  _ = keep
stackMod Pop   _ = pop
stackMod Push  x = push x
stackMod Alter x = alter x
stackMod PopSN x = popSndN x

ctrl :: Ctrl -> Word32 -> CtrlStack -> CtrlStack
ctrl c v (pc : xs) = let npc = succ pc in
  case c of
    NextPC ->       npc : xs
    Return ->             xs
    Call f -> f   : npc : xs 
    CondSkip
      | v == 0    -> succ npc : xs
      | otherwise -> npc      : xs
-}
 
{-
ctrl :: Ctrl -> Word32 -> Label -> CtrlStack -> CtrlStack
ctrl NextPC   _ npc xs = npc : xs
ctrl Return   _ npc xs = xs
ctrl CondSkip 0 npc xs = succ npc : xs
ctrl CondSkip _ npc xs = npc : xs
ctrl (Call f) _ npc xs = f:npc:xs
-}
{-
sim :: DataStack -> [Label] -> Word32
sim ds []       = top ds
sim ds (pc:cs) = {- -} trace (show pc ++ " " ++ show op ++ " " ++ show (x,y) ++ " " ++ show z ++ "   " ++ show cs' ++ "    " ++ show ds) $ {- -} sim ds' cs' where
  Just is = P.lookup pc instrMem
  (ia, ib, op, g, f) = decode is
  x = selInput ds ia
  y = selInput ds ib
  z = alu op x y 
  ds' = stackMod g z ds
  cs' = ctrl f z (pc : cs)
-}