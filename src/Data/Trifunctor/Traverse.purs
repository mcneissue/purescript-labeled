module Data.Trifunctor.Traverse where

import Prelude

import Control.Category.Tensor (grmap)
import Data.Iterated (class LabeledTensor, contraElim, elim, embed, project, singleton, unsingleton)
import Data.Symbol (class IsSymbol)
import Data.Trifunctor.Invariant (class Invariant, invmap)
import Data.Trifunctor.Monoidal (class Monoidal, class Semigroupal, combine, introduce)
import Prim.Row (class Cons, class Lacks)
import Type.Prelude (class ListToRow, class RowToList, Proxy(..))
import Type.RowList (Cons, Nil, RowList) as RL
import Type.RowList.Extra (head, tail) as RL

class Sequence1 :: Row Type -> Row Type -> Row Type -> Row Type -> RL.RowList Type -> (Type -> Type -> Type -> Type) -> Constraint
class Sequence1 r1' r2' r3' ro' rl' p | rl' -> p r1' r2' r3' ro'
  where
  sequence1 ::
    ∀ et1 et2 et3 eto
       t1  t2  t3 to
       i1  i2  i3 io
       a1  a2  a3
       r1  r2  r3 ro
       k.
    IsSymbol k =>

    Cons k a1 r1' r1 =>
    Lacks k r1' =>

    Cons k a2 r2' r2 =>
    Lacks k r2' =>

    Cons k a3 r3' r3 =>
    Lacks k r3' =>

    Cons k (p a1 a2 a3) ro' ro =>
    Lacks k ro' =>

    LabeledTensor et1 t1 i1 (->) =>
    LabeledTensor et2 t2 i2 (->) =>
    LabeledTensor et3 t3 i3 (->) =>
    LabeledTensor eto to io (->) =>

    ListToRow rl' ro' =>

    Semigroupal (->) t1 t2 t3 to p =>
    Invariant p =>

    Proxy (RL.Cons k (p a1 a2 a3) rl') -> eto ro -> p (et1 r1) (et2 r2) (et3 r3)

instance sequence1Base ::
  ( ListToRow RL.Nil ()
  ) =>
  Sequence1 () () () () RL.Nil p
  where
  sequence1 rl = unsingleton k >>> invmap (singleton k) (unsingleton k) (singleton k) (unsingleton k) (singleton k) (unsingleton k)
    where
    k = RL.head rl

instance sequence1Step ::
  ( IsSymbol k

  , Cons k a1 r1' r1
  , Lacks k r1'

  , Cons k a2 r2' r2
  , Lacks k r2'

  , Cons k a3 r3' r3
  , Lacks k r3'

  , Cons k (p a1 a2 a3) ro' ro
  , Lacks k ro'

  , ListToRow rl' ro'

  , Sequence1 r1' r2' r3' ro' rl' p
  ) =>
  Sequence1 r1 r2 r3 ro (RL.Cons k (p a1 a2 a3) rl') p
  where
  sequence1 rl = project k >>> grmap (sequence1 $ RL.tail rl) >>> combine >>> invmap (embed k) (project k) (embed k) (project k) (embed k) (project k)
    where
    k = RL.head rl

class Sequence :: Row Type -> Row Type -> Row Type -> Row Type -> RL.RowList Type -> (Type -> Type -> Type -> Type) -> Constraint
class Sequence r1 r2 r3 ro rl p | rl -> p r1 r2 r3 ro
  where
  sequence ::
    ∀ et1 et2 et3 eto
       t1  t2  t3 to
       i1  i2  i3 io.

    LabeledTensor et1 t1 i1 (->) =>
    LabeledTensor et2 t2 i2 (->) =>
    LabeledTensor et3 t3 i3 (->) =>
    LabeledTensor eto to io (->) =>

    ListToRow rl ro =>

    Monoidal (->) t1 i1 t2 i2 t3 i3 to io p =>
    Invariant p =>

    Proxy rl -> eto ro -> p (et1 r1) (et2 r2) (et3 r3)

instance sequenceBase ::
  Sequence () () () () RL.Nil p
  where
  sequence rl = contraElim >>> introduce >>> invmap elim contraElim elim contraElim elim contraElim

instance sequenceStep ::
  ( IsSymbol k

  , Cons k a1 r1' r1
  , Lacks k r1'

  , Cons k a2 r2' r2
  , Lacks k r2'

  , Cons k a3 r3' r3
  , Lacks k r3'

  , Cons k (p a1 a2 a3) ro' ro
  , Lacks k ro'

  , ListToRow rl' ro'

  , Sequence1 r1' r2' r3' ro' rl' p
  ) =>
  Sequence r1 r2 r3 ro (RL.Cons k (p a1 a2 a3) rl') p
  where
  sequence = sequence1

-- Convenient not to have to explicitly pass the RowList
sequence' ::
  ∀ et1 et2 et3 eto
    r1   r2  r3  ro
    t1   t2  t3  to
    i1   i2  i3  io
    rl p.
  RowToList ro rl =>
  ListToRow rl ro =>

  Sequence r1 r2 r3 ro rl p =>

  LabeledTensor et1 t1 i1 (->) =>
  LabeledTensor et2 t2 i2 (->) =>
  LabeledTensor et3 t3 i3 (->) =>
  LabeledTensor eto to io (->) =>

  Monoidal (->) t1 i1 t2 i2 t3 i3 to io p =>
  Invariant p =>
  eto ro -> p (et1 r1) (et2 r2) (et3 r3)
sequence' = sequence (Proxy :: _ rl)
