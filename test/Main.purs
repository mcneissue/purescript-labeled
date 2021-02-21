module Test.Main where

import Prelude

import Control.Alt (class Alt)
import Control.Plus (class Plus, empty)
import Data.Either (Either(..), either)
import Data.Either as Either
import Data.Foldable (class Foldable, length)
import Data.Profunctor (class Profunctor, dimap)
import Data.Profunctor.Monoidal (class Semigroupal, class Unital)
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Traverse (class BiInvariant, sequenceDemux, sequenceSwitch)
import Data.Tuple (Tuple(..))
import Data.Variant (SProxy(..), Variant, inj)
import Effect (Effect)
import Effect.Console (logShow)

-- TODO Add these instances upstream
newtype Fn a b = Fn (a -> b)

instance biinvariantFn :: BiInvariant Fn
  where
  biinvmap _ g h _ = dimap g h

runFn :: forall a b. Fn a b -> a -> b
runFn (Fn f) = f

instance profunctorFn :: Profunctor Fn where
  dimap f g (Fn x) = Fn $ dimap f g x

instance demuxFn :: Semigroupal (->) Either Either Tuple Fn where
  pzip (Tuple (Fn f) (Fn g)) = Fn \x -> either (Left <<< f) (Right <<< g) x

instance demuxativeFn :: Unital (->) Void Void Unit Fn where
  punit _ = Fn absurd

newtype Star' f a b = Star' (Star f a b)

runStar :: forall f a b. Star' f a b -> a -> f b
runStar (Star' (Star f)) = f

instance profunctorStar :: Functor f => Profunctor (Star' f) where
  dimap f g (Star' x) = Star' $ dimap f g x

instance biinvariantStar :: Functor f => BiInvariant (Star' f)
  where
  biinvmap _ g h _ = dimap g h

instance switchFn :: Alt f => Semigroupal (->) Tuple Either Tuple (Star' f) where
  pzip (Tuple (Star' (Star f)) (Star' (Star g))) = Star' $ Star \(Tuple a c) -> Either.choose (f a) (g c)

instance switchyStar :: Plus f => Unital (->) Unit Void Unit (Star' f) where
  punit _ = Star' $ Star \_ -> empty

test1 :: forall f x y. Foldable f => Show x => Fn (Variant (a :: x, b :: f y)) (Variant (a :: String, b :: Int))
test1 = sequenceDemux { a: Fn show, b: Fn length }

test2 :: forall b c. Star' Array { a :: b, b :: c } (Variant (a :: b, b :: Tuple c c ))
test2 = sequenceSwitch {a: Star' $ Star \x -> [x, x, x], b: Star' $ Star \x -> Tuple <$> pure x <*> pure x }

main :: Effect Unit
main = do
  logShow $ runFn test1 (inj (SProxy :: SProxy "a") 42 :: Variant (a :: Int, b :: Array Int))
  logShow $ runFn test1 (inj (SProxy :: SProxy "b") [1,2,3] :: Variant (a :: Int, b :: Array Int))
  logShow $ runStar test2 { a: 1, b: "lol" }
