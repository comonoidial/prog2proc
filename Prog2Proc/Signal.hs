module Prog2Proc.Signal where

import Control.Applicative

-- A minimalistic Signal implementation.
data Signal a = a :- Signal a

instance Functor Signal where
   fmap f (a :- as) = f a :- fmap f as

instance Applicative Signal where
   pure x = x :- pure x
   (f :- fs) <*> (a :- as) = f a :- (fs <*> as)

sample :: Signal a -> [a]
sample (a :- as) = a : sample as

simulate :: (Signal i -> Signal o) -> [i] -> [o]
simulate sf = sample . sf . foldr (:-) (error "simulate running out of inputs")
