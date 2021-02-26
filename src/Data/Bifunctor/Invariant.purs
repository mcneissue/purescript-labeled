module Data.Bifunctor.Invariant where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Profunctor (class Profunctor, dimap)
import Data.Profunctor.Star (Star)

type Invmap f = ∀ a a' b b'. (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> f a b -> f a' b'

class Invariant f
  where
  invmap :: Invmap f

invmapProfunctor :: ∀ p. Profunctor p => Invmap p
invmapProfunctor _ g h _ = dimap g h

invmapBifunctor :: ∀ t. Bifunctor t => Invmap t
invmapBifunctor f _ h _ = bimap f h

-- Instances

instance invariantFunction :: Invariant (->)
  where
  invmap = invmapProfunctor

instance invariantStar :: Functor f => Invariant (Star f)
  where
  invmap = invmapProfunctor
