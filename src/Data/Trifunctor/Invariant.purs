module Data.Trifunctor.Invariant where

type Invmap f = ∀ a a' b b' c c'. (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> (c -> c') -> (c' -> c) -> f a b c -> f a' b' c'

class Invariant f
  where
  invmap :: Invmap f
