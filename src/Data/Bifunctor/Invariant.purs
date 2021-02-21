module Data.Bifunctor.Invariant where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Profunctor (class Profunctor, dimap)
import Data.Profunctor.Star (Star)

class Invariant t
  where
  invmap :: ∀ a a' b b'. (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> t a b -> t a' b'

invmapProfunctor :: ∀ p a a' b b'. Profunctor p => (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> p a b -> p a' b'
invmapProfunctor _ g h _ = dimap g h

invmapBifunctor :: ∀ t a a' b b'. Bifunctor t => (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> t a b -> t a' b'
invmapBifunctor f _ h _ = bimap f h

-- Instances

instance invariantFunction :: Invariant (->)
  where
  invmap = invmapProfunctor

instance invariantStar :: Functor f => Invariant (Star f)
  where
  invmap = invmapProfunctor
