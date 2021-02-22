module Test.Main where

import Prelude

import Data.Bifunctor.Traverse (sequence')
import Data.Foldable (class Foldable, length)
import Data.Newtype (unwrap)
import Data.Profunctor.Star (Star(..))
import Data.Tuple.Nested (type (/\), (/\))
import Data.Variant (SProxy(..), Variant, inj)
import Effect (Effect)
import Effect.Console (logShow)

test1 :: ∀ f x y.
  Foldable f =>
  Show x =>
  Variant ( a :: x     , b :: f y ) ->
  Variant ( a :: String, b :: Int )
test1 = sequence'
  { a: show
  , b: length
  }

test2 :: ∀ a b.
  Star Array
             { a :: a, b :: b      }
    (Variant ( a :: a, b :: b /\ b ))
test2 = sequence'
  { a: Star \x -> [x, x, x]
  , b: Star \x -> (/\) <$> pure x <*> pure x
  }

main :: Effect Unit
main = do
  logShow $ test1 (inj (SProxy :: SProxy "a") 42 :: Variant (a :: Int, b :: Array Int))
  logShow $ test1 (inj (SProxy :: SProxy "b") [1,2,3] :: Variant (a :: Int, b :: Array Int))
  logShow $ unwrap test2 { a: 1, b: "lol" }
