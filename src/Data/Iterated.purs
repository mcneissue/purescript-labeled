module Data.Iterated where

import Prelude

import Control.Category.Tensor (class Associative, class Tensor, Iso, runit)
import Data.Bifunctor (class Bifunctor, rmap)
import Data.Either (Either(..), either)
import Data.Profunctor.Strong ((&&&))
import Data.Symbol (class IsSymbol, SProxy)
import Data.Tuple (Tuple, uncurry)
import Data.Variant (Variant, case_, inj, on)
import Prim.Row (class Cons, class Lacks)
import Record (delete, get, insert)
import Unsafe.Coerce (unsafeCoerce)

class Associative t p <= LabeledAssociative (e :: # Type -> Type) t p | e -> t
  where
  nest :: ∀ k a r r'. IsSymbol k => Lacks k r' => Cons k a r' r => SProxy k -> Iso p (t a (e r')) (e r)

embed :: ∀ e t k a r' r.
  LabeledAssociative e t (->) =>
  IsSymbol k =>
  Lacks k r' =>
  Cons k a r' r =>
  SProxy k -> t a (e r') -> e r
embed k = (nest k).fwd

project :: ∀ e t k a r' r.
  LabeledAssociative e t (->) =>
  IsSymbol k =>
  Lacks k r' =>
  Cons k a r' r =>
  SProxy k -> e r -> t a (e r')
project k = (nest k).bwd

instance labeledAssociativeRecord :: LabeledAssociative Record Tuple (->)
  where
  nest k = { fwd, bwd }
    where
    fwd = uncurry (insert k)
    bwd = get k &&& delete k

expandCons :: ∀ k v lt gt. IsSymbol k => Cons k v lt gt => SProxy k -> Variant lt -> Variant gt
expandCons _ = unsafeCoerce

instance labeledAssociativeVariant :: LabeledAssociative Variant Either (->)
  where
  nest k = { fwd, bwd }
    where
    fwd = either (inj k) (expandCons k)
    bwd = on k Left Right

class (LabeledAssociative e t p, Tensor t i p) <= LabeledTensor e t i p | e -> t i, t -> i, i -> t
  where
  point :: Iso p i (e ())

elim :: ∀ e t i.
  LabeledTensor e t i (->) =>
  i -> e ()
elim = point.fwd

contraElim :: ∀ e t i.
  LabeledTensor e t i (->) =>
  e () -> i
contraElim = point.bwd

singleton :: ∀ e t i k v r.
  IsSymbol k =>
  Cons k v () r =>
  Lacks k () =>
  Bifunctor t =>
  LabeledTensor e t i (->) =>
  SProxy k -> v -> e r
singleton k = embed k <<< rmap elim <<< runit.bwd

unsingleton :: ∀ e t i k v r.
  IsSymbol k =>
  Cons k v () r =>
  Lacks k () =>
  Bifunctor t =>
  LabeledTensor e t i (->) =>
  SProxy k -> e r -> v
unsingleton k = project k >>> rmap contraElim >>> runit.fwd

instance labeledTensorRecord :: LabeledTensor Record Tuple Unit (->)
  where
  point = { fwd, bwd }
    where
    fwd = mempty
    bwd = mempty

instance labeledTensorVariant :: LabeledTensor Variant Either Void (->)
  where
  point = { fwd, bwd }
    where
    fwd = absurd
    bwd = case_

