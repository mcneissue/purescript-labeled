module Test.Main where

import Prelude

import Data.Bifunctor.Invariant (class Invariant)
import Data.Bifunctor.Monoidal (class Semigroupal, class Unital, class Monoidal)
import Data.Bifunctor.Traverse (sequenceDemux, sequenceSwitch)
import Data.Either (Either)
import Data.Foldable (class Foldable, length)
import Data.Newtype (unwrap)
import Data.Profunctor (class Profunctor)
import Data.Profunctor.Star (Star(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Variant (SProxy(..), Variant, inj)
import Effect (Effect)
import Effect.Console (logShow)

-- TODO Add these instances upstream
newtype Fn a b = Fn (a -> b)

runFn :: forall a b. Fn a b -> a -> b
runFn (Fn f) = f

derive newtype instance profunctorFn :: Profunctor Fn
derive newtype instance invariantFn :: Invariant Fn
derive newtype instance eetSemigroupalFn :: Semigroupal (->) Either Either Tuple Fn
derive newtype instance eetUnitalFn :: Unital (->) Void Void Unit Fn
instance eetMonoidalFn :: Monoidal (->) Either Void Either Void Tuple Unit Fn

test1 :: ∀ f x y.
  Foldable f =>
  Show x =>
  Fn (Variant ( a :: x, b :: f y )) (Variant ( a :: String, b :: Int ))
test1 = sequenceDemux { a: Fn show, b: Fn length }

test2 :: ∀ a b.
  Star Array
    { a :: a, b :: b }
    (Variant ( a :: a, b :: b /\ b ))
test2 = sequenceSwitch
  { a: Star \x -> [x, x, x]
  , b: Star \x -> (/\) <$> pure x <*> pure x
  }

main :: Effect Unit
main = do
  logShow $ runFn test1 (inj (SProxy :: SProxy "a") 42 :: Variant (a :: Int, b :: Array Int))
  logShow $ runFn test1 (inj (SProxy :: SProxy "b") [1,2,3] :: Variant (a :: Int, b :: Array Int))
  logShow $ unwrap test2 { a: 1, b: "lol" }
