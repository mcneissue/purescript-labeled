module Data.Functor.InvariantExceptThatSomeoneAlreadyDefinedThis where

import Prelude

import Data.Functor.Contravariant (class Contravariant, cmap)

type Invmap f = ∀ a a'. (a -> a') -> (a' -> a) -> f a -> f a'

class Invariant f
  where
  invmap :: Invmap f

invmapFunctor :: ∀ f. Functor f => Invmap f
invmapFunctor f _ = map f

invmapContravariant :: ∀ f. Contravariant f => Invmap f
invmapContravariant _ f = cmap f
