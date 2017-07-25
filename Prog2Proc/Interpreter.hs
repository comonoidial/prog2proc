{-# LANGUAGE GADTs, Rank2Types #-}
module Prog2Proc.Interpreter where

import Data.STRef.Lazy
import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.ST.Lazy

import Prog2Proc.Signal

type SeqLogic s i o a = Program (SeqAction s i o) a

-- Program of commands represented as Freeer/Operational Monad.
data Program cmd a where
   Pure :: a                             -> Program cmd a
   Then :: cmd x -> (x -> Program cmd a) -> Program cmd a

instance Functor (Program cmd) where
   fmap f (Pure x    ) = Pure (f x)
   fmap f (c `Then` r) = c `Then` (fmap f . r)
     
instance Applicative (Program cmd) where
   pure x = Pure x
   Pure f     <*> a = fmap f a
   c `Then` r <*> a = c `Then` ((<*> a) . r)
     
instance Monad (Program cmd) where
  return x = Pure x
  Pure x     >>= k = k x
  c `Then` r >>= k = c `Then` (r >=> k)

command :: cmd a -> Program cmd a
command c = c `Then` Pure

-- Actions for sequential logic parametrized by an input and output types
data SeqAction s i o a where
   Clock   :: SeqAction s i o ()
   Receive :: SeqAction s i o i
   Emit    :: a -> SeqAction s i a ()
   Alloc   :: a -> SeqAction s i o (Ref s a)
   AllocArr:: Int -> SeqAction s i o (Ref s [a])
   Load    :: Ref s a -> SeqAction s i o a
   Store   :: Ref s a -> a -> SeqAction s i o ()
   Start   :: SeqLogic s j p a -> SeqAction s i o (Coproc s j p a)
   Finish  :: Coproc s j p a -> SeqAction s i o a
   Infuse  :: Coproc s j p x -> j -> SeqAction s i o ()
   Extract :: Coproc s j a x -> SeqAction s i o a

data Ref s a = Ref (STRef s a) | ArrRef (STRef s a) | IxRef Int (Ref s [a])

indexRef :: Int -> Ref s [a] -> Ref s a
indexRef = IxRef

newtype Coproc s j p a = Coproc (STRef s (CoProStatus, Maybe j, Maybe p, SeqLogic s j p a))

data CoProStatus = Starting | Active | Finished deriving (Eq, Show)

-- Interpreting sequential logic as a maybe signal function.
interpretSeqLogic :: (forall s. SeqLogic s i o ()) -> Signal (Maybe i) -> Signal (Maybe o)
interpretSeqLogic prog is = runST (interpretSL prog [] is)

data CoproElem s = forall j p a. CoproElem (Coproc s j p a)

interpretSL :: SeqLogic s i o () -> [CoproElem s] -> Signal (Maybe i) -> ST s (Signal (Maybe o))
interpretSL prog cps (mi :- is) = do
   (cps', next, (mi', mo)) <- interpretCycle (mi, Nothing) cps prog
   when (isJust mi') $ error "dropping unused input"
   rs <- interpretSL next cps' is
   return (mo :- rs)

interpretCycle :: (Maybe i, Maybe o) -> [CoproElem s] -> forall a. SeqLogic s i o a -> ST s ([CoproElem s], SeqLogic s i o a, (Maybe i, Maybe o))
interpretCycle (mi, mo) cps (Pure x         ) = return (cps, Pure x, (mi, mo))
interpretCycle (mi, mo) cps (Clock   `Then` r) = do
   cps' <- filterM runCoproCycle cps                      -- filter out finished copro's
   return (cps', r (), (mi, mo))
interpretCycle (mi, mo) cps (Receive `Then` r) = case mi of
   Nothing -> do                                          -- block on no input value
      mapM_ runCoproCycle cps
      return (cps, Receive `Then` r, (mi, mo))
   Just i  -> interpretCycle (Nothing, mo) cps (r i)      -- clearing input thus only one receive per cycle
interpretCycle (mi, mo) cps (Emit x `Then` r) = case mo of
   Nothing -> interpretCycle (mi, Just x) cps (r ())
   Just _  -> do                                          -- block on filled output channel
      mapM_ runCoproCycle cps
      return (cps, Emit x `Then` r, (mi, mo))
interpretCycle (mi, mo) cps (Alloc i `Then` r) = do
   p <- newSTRef i
   interpretCycle (mi, mo) cps (r (Ref p))
interpretCycle (mi, mo) cps (AllocArr n `Then` r) = do
   p <- newSTRef (replicate n undefined)
   interpretCycle (mi, mo) cps (r (ArrRef p))
interpretCycle (mi, mo) cps (Load p `Then` r) = do
   x <- readRef p
   interpretCycle (mi, mo) cps (r x)
interpretCycle (mi, mo) cps (Store p x `Then` r) = do
   writeRef p x
   interpretCycle (mi, mo) cps (r ())
interpretCycle (mi, mo) cps (Start p `Then` r) = do
   cpr <- fmap Coproc (newSTRef (Starting, Nothing, Nothing, p))          -- actual start of Copro is delayed till next cycle by Starting status
   let cpx = CoproElem cpr
   interpretCycle (mi, mo) (cpx : cps) (r cpr)
interpretCycle (mi, mo) cps (Finish (Coproc cpr) `Then` r) = do
   (s, ci, co, p) <- readSTRef cpr
   case p of
      _ | s == Finished -> error "coprocessor already finished"
      _ | isJust ci || isJust co -> error "coprocessor can't finish with filled channels"
      Pure x -> do
         writeSTRef cpr (Finished, Nothing, Nothing, p)
         interpretCycle (mi, mo) cps (r x)
      _      -> do
         mapM_ runCoproCycle cps
         return (cps, Finish (Coproc cpr) `Then` r, (mi, mo))
interpretCycle (mi, mo) cps (Infuse (Coproc cpr) xi `Then` r) = do
   (s, ci, co, p) <- readSTRef cpr
   case ci of
     Just _ -> do                        -- block on filled channel
       mapM_ runCoproCycle cps
       return (cps, Infuse (Coproc cpr) xi `Then` r, (mi, mo))
     Nothing -> do
       writeSTRef cpr (s, Just xi, co, p)
       interpretCycle (mi, mo) cps (r ())
interpretCycle (mi, mo) cps (Extract (Coproc cpr) `Then` r) = do
   (s, ci, co, p) <- readSTRef cpr
   case co of
     Nothing -> do                       -- block on empty channel
       mapM_ runCoproCycle cps
       return (cps, Extract (Coproc cpr) `Then` r, (mi, mo))
     Just xo -> do
       writeSTRef cpr (s, ci, Nothing, p)
       interpretCycle (mi, mo) cps (r xo)

runCoproCycle :: CoproElem s -> ST s Bool
runCoproCycle (CoproElem (Coproc cp)) = do
   (s, mi, mo, p) <- readSTRef cp
   case s of
      Starting -> do
         writeSTRef cp (Active, mi, mo, p)  -- make active state
         return True
      Active   -> do
        (_, p', (mi', mo')) <- interpretCycle (mi, mo) [] p     -- FIXME we make unchecked assumption here that a copro doesn't contain nested copro's
        writeSTRef cp (Active, mi', mo', p')
        return True
      Finished -> return False

readRef :: Ref s a -> ST s a
readRef (Ref r) = readSTRef r
readRef (IxRef i (ArrRef r)) = fmap (!!i) (readSTRef r)
readRef (IxRef i r) = fmap (!!i) (readRef r)
readRef (ArrRef _) = error "arrays can only be read per element"

writeRef :: Ref s a -> a -> ST s ()
writeRef (Ref r) x = writeSTRef r x
writeRef (IxRef i r) x = modifyRef r ((\(xs, _:ys) -> xs ++ x : ys) . splitAt i)
writeRef (ArrRef _) x = error "arrays can only be written per element"

modifyRef :: Ref s a -> (a -> a) -> ST s ()
modifyRef (Ref r) f = modifySTRef r f
modifyRef (IxRef i r) f = modifyRef r ((\(xs, x:ys) -> xs ++ f x : ys) . splitAt i)
modifyRef (ArrRef r) f = modifySTRef r f
