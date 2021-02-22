module Data.Trifunctor.Invariant where

class Invariant t
  where
  invmap :: ∀ a a' b b' c c'. (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> (c -> c') -> (c' -> c) -> t a b c -> t a' b' c'
