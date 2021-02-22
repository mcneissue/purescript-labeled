module Data.Bifunctor.Traverse where

import Prelude

import Data.Bifunctor.Invariant (class Invariant, invmap)
import Data.Bifunctor.Monoidal (class Semigroupal, class Unital, combine, introduce)
import Data.Iterated (class LabeledAssociative, class LabeledTensor, embed, point, project)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant.Internal (RLProxy(..))
import Prim.Row (class Cons, class Lacks)
import Record (get)
import Type.RowList as RL

class SequenceMonoidal et1 et2 (rl :: RL.RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p | r -> p ri ro
  where
  sequenceMonoidal :: RLProxy rl -> Record r -> p (et1 ri) (et2 ro)

instance emptySequenceMonoidal ::
  ( Invariant p
  , Unital (->) u1 u2 Unit p
  , Semigroupal (->) t1 t2 Tuple p
  , LabeledTensor et1 t1 u1 (->)
  , LabeledTensor et2 t2 u2 (->)
  ) => SequenceMonoidal et1 et2 RL.Nil r () () p
  where
  sequenceMonoidal _ _ = invmap point.fwd point.bwd point.fwd point.bwd (introduce unit :: p u1 u2)

instance stepSequenceMonoidal ::
  ( Invariant p
  , Semigroupal (->) t1 t2 Tuple p
  , IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , Lacks x ro'
  , Lacks x ri'
  , LabeledAssociative et1 t1 (->)
  , LabeledAssociative et2 t2 (->)
  , SequenceMonoidal et1 et2 rl r ri' ro' p
  ) => SequenceMonoidal et1 et2 (RL.Cons x (p i o) rl) r ri ro p
  where
  sequenceMonoidal _ r = invmap (embed k) (project k) (embed k) (project k) (combine (Tuple (get k r) rest) :: p (t1 i (et1 ri')) (t2 o (et2 ro')))
    where
    k :: SProxy x
    k = SProxy
    rest :: p (et1 ri') (et2 ro')
    rest = sequenceMonoidal (RLProxy :: _ rl) r

sequenceMux
  :: ∀ r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Record Record rl r ri ro p
  => Record r
  -> p (Record ri) (Record ro)
sequenceMux = sequenceMonoidal (RLProxy :: _ rl)

sequenceDemux
  :: ∀ r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Variant Variant rl r ri ro p
  => Record r
  -> p (Variant ri) (Variant ro)
sequenceDemux = sequenceMonoidal (RLProxy :: _ rl)

sequenceSwitch
  :: ∀ r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Record Variant rl r ri ro p
  => Record r
  -> p (Record ri) (Variant ro)
sequenceSwitch = sequenceMonoidal (RLProxy :: _ rl)

sequenceSplice
  :: ∀ r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Variant Record rl r ri ro p
  => Record r
  -> p (Variant ri) (Record ro)
sequenceSplice = sequenceMonoidal (RLProxy :: _ rl)
