module Data.Functor.Traverse where

import Prelude

import Control.Category.Tensor (grmap)
import Data.Functor.InvariantExceptThatSomeoneAlreadyDefinedThis (class Invariant, invmap)
import Data.Functor.Monoidal (class Monoidal, class Semigroupal, combine, introduce)
import Data.Iterated (class LabeledTensor, contraElim, elim, embed, project, singleton, unsingleton)
import Data.Symbol (class IsSymbol)
import Prim.Row (class Cons, class Lacks)
import Type.Data.RowList (RLProxy(..))
import Type.Prelude (class ListToRow, class RowToList)
import Type.RowList (Cons, Nil, kind RowList) as RL
import Type.RowList.Extra (head, tail) as RL


class Sequence1
  (r1' :: # Type)
  (ro' :: # Type)
  (rl' :: RL.RowList)
  (f :: Type -> Type)
  | rl' -> f r1' ro'
  where
  sequence1 ::
    ∀ et1 eto
       t1 to
       i1 io
       a1
       r1 ro
       k.
    IsSymbol k =>

    Cons k a1 r1' r1 =>
    Lacks k r1' =>

    Cons k (f a1) ro' ro =>
    Lacks k ro' =>

    LabeledTensor et1 t1 i1 (->) =>
    LabeledTensor eto to io (->) =>

    ListToRow rl' ro' =>

    Semigroupal (->) t1 to f =>
    Invariant f =>

    RLProxy (RL.Cons k (f a1) rl') -> eto ro -> f (et1 r1)

instance sequence1Base ::
  ( ListToRow RL.Nil ()
  ) =>
  Sequence1 () () RL.Nil f
  where
  sequence1 rl = unsingleton k >>> invmap (singleton k) (unsingleton k)
    where
    k = RL.head rl

instance sequence1Step ::
  ( IsSymbol k

  , Cons k a1 r1' r1
  , Lacks k r1'

  , Cons k (f a1) ro' ro
  , Lacks k ro'

  , ListToRow rl' ro'

  , Sequence1 r1' ro' rl' f
  ) =>
  Sequence1 r1 ro (RL.Cons k (f a1) rl') f
  where
  sequence1 rl = project k >>> grmap (sequence1 $ RL.tail rl) >>> combine >>> invmap (embed k) (project k)
    where
    k = RL.head rl

class Sequence
  (r1 :: # Type)
  (ro :: # Type)
  (rl :: RL.RowList)
  (f :: Type -> Type)
  | rl -> f r1 ro
  where
  sequence ::
    ∀ et1 eto
       t1 to
       i1 io.

    LabeledTensor et1 t1 i1 (->) =>
    LabeledTensor eto to io (->) =>

    ListToRow rl ro =>

    Monoidal (->) t1 i1 to io f =>
    Invariant f =>

    RLProxy rl -> eto ro -> f (et1 r1)

instance sequenceBase ::
  Sequence () () RL.Nil f
  where
  sequence rl = contraElim >>> introduce >>> invmap elim contraElim

instance sequenceStep ::
  ( IsSymbol k

  , Cons k a1 r1' r1
  , Lacks k r1'

  , Cons k (f a1) ro' ro
  , Lacks k ro'

  , ListToRow rl' ro'

  , Sequence1 r1' ro' rl' f
  ) =>
  Sequence r1 ro (RL.Cons k (f a1) rl') f
  where
  sequence = sequence1

-- Convenient not to have to explicitly pass the RowList
sequence' ::
  ∀ et1 eto
    r1   ro
    t1   to
    i1   io
    rl f.
  RowToList ro rl =>
  ListToRow rl ro =>

  Sequence r1 ro rl f =>

  LabeledTensor et1 t1 i1 (->) =>
  LabeledTensor eto to io (->) =>

  Monoidal (->) t1 i1 to io f =>
  Invariant f =>
  eto ro -> f (et1 r1)
sequence' = sequence (RLProxy :: _ rl)
