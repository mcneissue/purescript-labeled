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
import Data.Profunctor.Traverse (foldDemux, foldSwitch)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Effect (Effect)
import Effect.Class.Console (log)


-- TODO Add these instances upstream
newtype Fn a b = Fn (a -> b)

instance profunctorFn :: Profunctor Fn where
  dimap f g (Fn x) = Fn $ dimap f g x

instance demuxFn :: Semigroupal (->) Either Either Tuple Fn where
  pzip (Tuple (Fn f) (Fn g)) = Fn \x -> either (Left <<< f) (Right <<< g) x

instance demuxativeFn :: Unital (->) Void Void Unit Fn where
  punit _ = Fn absurd

newtype Star' f a b = Star' (Star f a b)

instance profunctorStar :: Functor f => Profunctor (Star' f) where
  dimap f g (Star' x) = Star' $ dimap f g x

instance switchFn :: Alt f => Semigroupal (->) Tuple Either Tuple (Star' f) where
  pzip (Tuple (Star' (Star f)) (Star' (Star g))) = Star' $ Star \(Tuple a c) -> Either.choose (f a) (g c)

instance switchyStar :: Plus f => Unital (->) Unit Void Unit (Star' f) where
  punit _ = Star' $ Star \_ -> empty

test1 :: forall f x y. Foldable f => Show x => Fn (Variant (a :: x, b :: f y)) (Variant (a :: String, b :: Int))
test1 = foldDemux { a: Fn show, b: Fn length }

test2 :: forall f b. Applicative f => Plus f => Star' f { a :: b } (Variant (a :: b ))
test2 = foldSwitch {a: Star' $ Star \x -> pure x }

main :: Effect Unit
main = do
  log "🍝"
  log "You should add some tests."
