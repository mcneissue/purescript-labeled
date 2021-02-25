module Data.Iterated where

import Prelude

import Control.Category.Tensor (class Associative, class Cartesian, class Tensor, Iso, diagonal, gbimap, grmap, runit, terminal)
import Data.Either (Either(..), either)
import Data.Newtype (un)
import Data.Op (Op(..))
import Data.Profunctor.Strong ((&&&))
import Data.Symbol (class IsSymbol, SProxy)
import Data.Tuple (Tuple, uncurry)
import Data.Variant (Variant, case_, inj, on)
import Prim.Row (class Cons, class Lacks)
import Prim.RowList (class RowToList)
import Record (delete, get, insert)
import Type.Row as Row
import Type.RowList (Cons, Nil) as RowList
import Type.RowList (class ListToRow, RLProxy(..))
import Type.RowList.Extra (head, tail) as RowList
import Unsafe.Coerce (unsafeCoerce)

class Associative t p <= LabeledAssociative (e :: # Type -> Type) t p | e -> t
  where
  nest :: ∀ k a r r'. IsSymbol k => Lacks k r' => Cons k a r' r => SProxy k -> Iso p (t a (e r')) (e r)

embed :: ∀ e t p k a r' r.
  LabeledAssociative e t p =>
  IsSymbol k =>
  Lacks k r' =>
  Cons k a r' r =>
  SProxy k -> p (t a (e r')) (e r)
embed k = (nest k).fwd

project :: ∀ e t p k a r' r.
  LabeledAssociative e t p =>
  IsSymbol k =>
  Lacks k r' =>
  Cons k a r' r =>
  SProxy k -> p (e r) (t a (e r'))
project k = (nest k).bwd

instance flipLabeledAssociative :: LabeledAssociative e t (->) => LabeledAssociative e t Op
  where
  nest k = let { fwd, bwd } = nest k in { fwd: Op bwd, bwd: Op fwd }

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

instance flipLabeledTensor :: LabeledTensor e t i (->) => LabeledTensor e t i Op
  where
  point = let { fwd, bwd } = point in { fwd: Op bwd, bwd: Op fwd }

elim :: ∀ e t i p.
  LabeledTensor e t i p =>
  p i (e ())
elim = point.fwd

contraElim :: ∀ e t i p.
  LabeledTensor e t i p =>
  p (e ()) i
contraElim = point.bwd

singleton :: ∀ e t i p k v r.
  IsSymbol k =>
  Cons k v () r =>
  Lacks k () =>
  LabeledTensor e t i p =>
  SProxy k -> p v (e r)
singleton k = embed k <<< grmap elim <<< runit.bwd

unsingleton :: ∀ e t i p k v r.
  IsSymbol k =>
  Cons k v () r =>
  Lacks k () =>
  LabeledTensor e t i p =>
  SProxy k -> p (e r) v
unsingleton k = project k >>> gbimap identity contraElim >>> runit.fwd

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

class Diagonal rl v r | rl -> v r
  where
  ldiagonal :: ∀ e t i p.
    LabeledTensor e t i p =>
    Cartesian t i p =>
    ListToRow rl r =>
    RLProxy rl -> p v (e r)

instance diagonalBase :: Diagonal RowList.Nil v ()
  where
  ldiagonal _ = terminal >>> point.fwd

instance diagonalStep ::
  ( IsSymbol k
  , Lacks k r'

  , ListToRow rl' r'

  , Row.Cons k v r' r
  , Diagonal rl' v r'
  ) =>
  Diagonal (RowList.Cons k v rl') v r
  where
  ldiagonal rl = diagonal >>> gbimap identity (ldiagonal $ RowList.tail rl) >>> embed k
    where
    k = RowList.head rl

ldiagonal' :: ∀ e t i p rl v r.
  ListToRow rl r =>
  RowToList r rl =>

  Diagonal rl v r =>

  LabeledTensor e t i p =>
  Cartesian t i p =>
  p v (e r)
ldiagonal' = ldiagonal (RLProxy :: _ rl)

duplicateRecord :: ∀ rl v r.
  ListToRow rl r =>
  RowToList r rl =>

  Diagonal rl v r =>

  v -> Record r
duplicateRecord = ldiagonal'

mergeVariant :: ∀ rl v r.
  ListToRow rl r =>
  RowToList r rl =>

  Diagonal rl v r =>
  Variant r -> v
mergeVariant = un Op ldiagonal'
