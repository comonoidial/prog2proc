module Tests.ManualTrans where

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


binGCD :: Word32 -> Word32 -> Word32       
binGCD x 0 = x
binGCD x y =
  let a = dropZeros x in
  let b = dropZeros y in
  let (s,g) = (min a b, max a b) in
  binGCD s (g - s) <<< countZeros (x .|. y)

dropZeros :: Word32 -> Word32
dropZeros i = i >>> countZeros i

countZeros :: Word32 -> Int
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

countZeros :: Word32 -> Int
countZeros n = if odd n 
  then 0 
  else
    let m = n >>> 1 in
    let c = countZeros m in
    c + 1
-}

{-  -- *** Conversion to continuation passing style

x @@ f = f x

binGCD :: Word32 -> Word32 -> Word32       
binGCD x y k = 
  if (y == 0) then k x
  else
    dropZeros x
      (\a -> dropZeros y
        (\b -> (max a b) @@
          (\g -> (min a b) @@
            (\s -> (g - s) @@
              (\d -> binGCD s d
                (\r -> (x .|. y) @@
                  (\o -> countZeros o
                    (\e -> k (r <<< e)))))))))

dropZeros :: Word32 -> Word32
dropZeros i k = 
  countZeros i 
    (\s -> k (i >>> s))

countZeros :: Word32 -> Int
countZeros n k = if odd n 
  then k 0 
  else
    (n >> 1) @@
      (\m -> countZeros m 
        (\c -> k (c + 1)))
-}

{-  -- *** Translation into stack based step function
data State = GCD Word32 Word32 | DropZs Word32 | CountZs Word32 | R Word32 | R' Int | N1 Word32 Word32 Word32 Word32 Word32 | N2 Word32 Word32 Word32 Word32 Word32 Word32 
  | N3 Word32 Word32 Word32 Word32 Word32 Word32 Word32 | N4 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 | N5 Word32  Word32
data Context = CA Word32 Word32 | CB Word32 Word32 Word32 | CC Word32 Word32 Word32 Word32 Word32 Word32 Word32 | CD Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 Word32 | CE Word32 | CF Word32 Word32
type ControlStack  = [Context]
step :: State -> ControlStack -> (State, ControlStack)
step (GCD x y)              cs                          = if y == 0
                                                     then (R x                 , cs)
                                                     else (DropZs x            , CA x y : cs)
step (R a)                  (CA x y               : cs) = (DropZs y            , CB x y a : cs)
step (R b)                  (CB x y a             : cs) = (N1 x y a b g        , cs) where g = max a b
step (N1 x y a b g)         cs                          = (N2 x y a b g s      , cs) where s = min a b
step (N2 x y a b g s)       cs                          = (N3 x y a b g        , cs) where d = g - s
step (N3 x y a b g s d)     cs                          = (BinGCD s d          , CC x y a b g s d : cs)
step (R r)                  (CC x y a b s g d     : cs) = (N4 x y a b s g d r o, cs) where o = x .|. y
step (N4 x y a b s g d r o) cs                          = (CountZs o           , CD x y a b s g d r o : cs)
step (R' e)                 (CD x y a b s g d r o : cs) = (R (r <<< e)         , cs)
step (DropZs i)             cs                          = (CountZs i           , CE i : cs)
step (R' s)                 (CE i                 : cs) = (R (i >>> s)         , cs)
step (CountZs n)            cs                          = if odd n
                                                     then (R' 0                , cs)
                                                     else (N5 n m              , cs) where m = n >>> 1
step (N5 n m)               cs                          = (CountZs m           , CF n m : cs)
step (R' c)                 (CF n m               : cs) = (R' (c + 1)          , cs)

sim :: State -> ControlStack -> Word32
sim (R x) [] = x
sim s     cs = let (s' ,cs') = step s c in sim s' cs'
-}

{- -- *** Introducing data stack to avoid copying around many values from state to context and back
data State = GCD | DropZs | CntZs | Ret | N1 | N2 | N3 | N4 | N5
data Context = CA | CB | CC | CD | CE | CF
type ControlStack  = [Context]
type DataStack = [Word32]
step ::  State -> ControlStack -> DataStack -> (State, ControlStack, DataStack)
step GCD    cs                (y:x:ds) = if y == 0
                                    then (Ret   , cs   ,             x:ds)
                                    else (DropZs, CA:cs,         x:y:x:ds)
step Ret    (CA:cs)         (a:y:x:ds) = (DropZs, CB:cs,       y:a:y:x:ds)
step Ret    (CB:cs)       (b:a:y:x:ds) = (N1    , cs   ,     g:b:a:y:x:ds) where g = max a b
step N1     cs          (g:b:a:y:x:ds) = (N2    , cs   ,   s:g:b:a:y:x:ds) where s = min a b
step N2     cs        (s:g:b:a:y:x:ds) = (N3    , cs   , d:s:g:b:a:y:x:ds) where d = g - s
step N3     cs      (d:s:g:b:a:y:x:ds) = (BinGCD, CC:cs, d:s:g:b:a:y:x:ds)
step Ret    (CC:cs)   (r:g:b:a:y:x:ds) = (N4    , cs   , o:r:g:b:a:y:x:ds) where o = x .|. y
step N4     cs      (o:r:g:b:a:y:x:ds) = (CntZs , CD:cs, o:r:g:b:a:y:x:ds)
step Ret    (CD:cs) (e:r:g:b:a:y:x:ds) = (Ret   , cs   ,             l:ds) where l = r <<< e
step DropZs cs                  (i:ds) = (CntZs , CE:cs,           i:i:ds)
step Ret    (CE:cs)           (s:i:ds) = (Ret   , cs   ,             r:ds) where r = i >>> s
step CntZs  cs                  (n:ds) = if odd n
                                    then (Ret   ,cs    ,             z:ds) where z = 0
                                    else (N5    ,cs    ,           m:n:ds) where m = n >>> 1
step N5     cs                (m:n:ds) = (CntZs, CF:cs ,           m:n:ds)
step Ret    (CF:cs)           (c:n:ds) = (Ret  , cs    ,             p:ds) where p = c + 1

sim :: DataStack -> State -> ControlStack -> Word32
sim ds Ret [] = top ds
sim ds s   cs = let (s', cs' ,ds') = step s cs ds in sim ds' s' cs'
-}

{- -- *** Optimizing control
data Label = GCD | T1 | E1 | CA | CB | N1 | N2 | CC | N4 | CD | DropZs | CE | CntZs | T2 | E2 | CF | Halt deriving Enum
type ControlStack  = [Label]
type DataStack = [Word32]
type ControlFun = Label -> ControlStack -> Word32 -> (Label, ControlStack)
call f pc cs = (f, succ pc : cs)
ret _ []     = (Halt, [])
ret _ (c:cs) = (c, cs)
next pc cs   = (succ pc, cs)
jump f _ cs = (f, cs)
branch e True pc cs = (succ pc, cs)
branch e False pc cs = (e, cs)

step ::  Label -> DataStack -> (ControlFun, DataStack)
step GCD              (y:x:ds) = (branch E1 z,           y:x:ds) where z = y == 0
step T1               (y:x:ds) = (ret        ,             x:ds)
step E1               (y:x:ds) = (call DropZs,         x:y:x:ds)
step CA             (a:y:x:ds) = (call DropZs,       y:a:y:x:ds)
step CB           (b:a:y:x:ds) = (next       ,     g:b:a:y:x:ds) where g = max a b
step N1         (g:b:a:y:x:ds) = (next       ,   s:g:b:a:y:x:ds) where s = min a b
step N2       (s:g:b:a:y:x:ds) = (call BinGCD, d:s:g:b:a:y:x:ds) where d = g - s          -- note fused step N2/N3
step CC       (r:g:b:a:y:x:ds) = (call CntZs , o:r:g:b:a:y:x:ds) where o = x .|. y        -- note fused with N4
step CD     (e:r:g:b:a:y:x:ds) = (ret        ,             l:ds) where l = r <<< e
step DropZs             (i:ds) = (call CntZs ,           i:i:ds)
step CE               (s:i:ds) = (ret        ,             r:ds) where r = i >>> s
step CntZs              (n:ds) = (branch E2 o,             n:ds) where o = odd n
step T2                 (n:ds) = (ret        ,             z:ds) where z = 0
step E2                 (n:ds) = (call CntZs ,           m:n:ds) where m = n >>> 1        -- note fused with N5
step CF               (c:n:ds) = (ret        ,             p:ds) where p = c + 1

sim :: DataStack -> Label -> ControlStack -> Word32
sim ds Halt [] = top ds
sim ds pc   cs = sim ds' pc' cs' where
   let (cf ,ds') = step pc ds
   (pc', cs') = cf pc cs
-}

