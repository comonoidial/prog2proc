{-# LANGUAGE GADTs, Rank2Types #-}
module Prog2Proc.Interpreter where

import Data.STRef.Lazy
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
   Load    :: Ref s a -> SeqAction s i o a
   Store   :: Ref s a -> a -> SeqAction s i o ()
   Start   :: SeqLogic s () () a -> SeqAction s i o (Coproc s a)
   Finish  :: Coproc s a -> SeqAction s i o a

data Ref s a = Ref (STRef s a) | IxRef Int (Ref s [a])

indexRef :: Int -> Ref s [a] -> Ref s a
indexRef = IxRef

newtype Coproc s a = Coproc (STRef s (CoProStatus, SeqLogic s () () a))

data CoProStatus = Active | CycleRun | Finished deriving Show

-- Interpreting sequential logic as a maybe signal function.
interpretSeqLogic :: (forall s. SeqLogic s i o ()) -> Signal (Maybe i) -> Signal (Maybe o)
interpretSeqLogic prog is = runST (interpretSL prog [] is)

data CoproElem s = forall a. CoproElem (Coproc s a)

interpretSL :: SeqLogic s i o () -> [CoproElem s] -> Signal (Maybe i) -> ST s (Signal (Maybe o))
interpretSL prog cps (mi :- is) = do
   (cps', next, mo) <- interpretCycle (mi, Nothing) cps prog
   rs <- interpretSL next cps' is
   return (mo :- rs)

interpretCycle :: (Maybe i, Maybe o) -> [CoproElem s] -> forall a. SeqLogic s i o a -> ST s ([CoproElem s], SeqLogic s i o a, Maybe o)
interpretCycle (mi, mo) cps (Pure x         ) = return (cps, Pure x, mo)
interpretCycle (mi, mo) cps (Clock   `Then` r) = do
   cps' <- filterM runCoproCycle cps                      -- filter out finished copro's
   return (cps', r ()   , mo)
interpretCycle (mi, mo) cps (Receive `Then` r) = case mi of
   Nothing -> do                                          -- block on no input value
      mapM_ runCoproCycle cps
      return (cps, Receive `Then` r, mo)
   Just i  -> interpretCycle (Nothing, mo) cps (r i)      -- clearing input thus only one receive per cycle
interpretCycle (mi, mo) cps (Emit x  `Then` r) = case mo of
   Nothing -> interpretCycle (mi, Just x) cps (r ())
   Just _  -> error "multiple emits in one cycle"
interpretCycle (mi, mo) cps (Alloc i `Then` r) = do
   p <- newSTRef i
   interpretCycle (mi, mo) cps (r (Ref p))
interpretCycle (mi, mo) cps (Load p `Then` r) = do
   x <- readRef p
   interpretCycle (mi, mo) cps (r x)
interpretCycle (mi, mo) cps (Store p x `Then` r) = do
   writeRef p x
   interpretCycle (mi, mo) cps (r ())
interpretCycle (mi, mo) cps (Start p `Then` r) = do
   cpr <- fmap Coproc (newSTRef (Active, p))            -- TODO maybe delay input by starting with CycleRun status
   let cpx = CoproElem cpr
   interpretCycle (mi, mo) (cpx : cps) (r cpr)
interpretCycle (mi, mo) cps (Finish (Coproc cpr) `Then` r) = do
   (s, p) <- readSTRef cpr
   p' <- case s of        -- TODO decide if no delay copro result is wanted and feasible in hardware
     Finished -> error "coprocessor already finished"
     CycleRun -> return p
     Active -> do
       (_, px, _) <- interpretCycle (Nothing, Nothing) [] p     -- FIXME we make unchecked assumption here that a copro doesn't contain nested copro's
       writeSTRef cpr (CycleRun, px)
       return px
   case p' of 
      Pure x -> do
         writeSTRef cpr (Finished, p')
         interpretCycle (mi, mo) cps (r x)
      _      -> do
         mapM_ runCoproCycle cps
         return (cps, Finish (Coproc cpr) `Then` r, mo)

runCoproCycle :: CoproElem s -> ST s Bool
runCoproCycle (CoproElem (Coproc cp)) = do
   (s, p) <- readSTRef cp
   case s of
      CycleRun -> do
         writeSTRef cp (Active, p)
         return True
      Active   -> do
        (_, p', _) <- interpretCycle (Nothing, Nothing) [] p     -- FIXME we make unchecked assumption here that a copro doesn't contain nested copro's
        writeSTRef cp (Active, p')
        return True
      Finished -> return False

readRef :: Ref s a -> ST s a
readRef (Ref r) = readSTRef r
readRef (IxRef i r) = fmap (!!i) (readRef r)

writeRef :: Ref s a -> a -> ST s ()
writeRef (Ref r) x = writeSTRef r x
writeRef (IxRef i r) x = modifyRef r ((\(xs, _:ys) -> xs ++ x : ys) . splitAt i)

modifyRef :: Ref s a -> (a -> a) -> ST s ()
modifyRef (Ref r) f = modifySTRef r f
modifyRef (IxRef i r) f = modifyRef r ((\(xs, x:ys) -> xs ++ f x : ys) . splitAt i)
