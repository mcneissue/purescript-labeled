module Data.Bifunctor.Traverse where

import Prelude

import Data.Either (Either(..))
import Data.Profunctor (dimap)
import Data.Profunctor.Monoidal (class Semigroupal, class Unital, punit, pzip)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..))
import Data.Variant (Variant, case_, inj, on)
import Data.Variant.Internal (RLProxy(..))
import Prim.Row (class Cons, class Lacks)
import Record (delete, get, insert)
import Type.Proxy (Proxy(..), Proxy3(..))
import Type.RowList as RL
import Unsafe.Coerce (unsafeCoerce)

class BiInvariant (f :: Type -> Type -> Type) where
  biinvmap :: forall a a' b b'. (a -> a') -> (a' -> a) -> (b -> b') -> (b' -> b) -> f a b -> f a' b'

class ComputeExtension (t :: Type -> Type -> Type) (e :: # Type -> Type) (u :: Type) | t -> e u where
  embed :: forall s a r r'. IsSymbol s => Lacks s r' => Cons s a r' r => SProxy s -> t a (e r') -> e r
  project :: forall s a r r'. IsSymbol s => Lacks s r' => Cons s a r' r => SProxy s -> e r -> t a (e r')
  elim :: Proxy3 t -> u -> e ()
  contraElim :: Proxy3 t -> e () -> u

instance computeExtensionTuple :: ComputeExtension Tuple Record Unit where
  embed s (Tuple a r') = insert s a r'
  project s r = Tuple (get s r) (delete s r)
  contraElim _ _ = unit
  elim _ _ = {}

instance computeExtensionEither :: ComputeExtension Either Variant Void where
  embed s e = case e of
    Left o -> inj s o
    Right v -> expandCons s v
    where
        -- A version of `expand` that works with a Cons constraint rather than a Union constraint
    expandCons :: forall s i lt gt. IsSymbol s => Cons s i lt gt => SProxy s -> Variant lt -> Variant gt
    expandCons l v = unsafeCoerce v
  project s v = on s Left Right v
  contraElim _ = case_
  elim _ = absurd

class
  ( ComputeExtension t1 et1 u1
  , ComputeExtension t2 et2 u2
  ) <= SequenceMonoidal t1 t2 u1 u2 et1 et2 (rl :: RL.RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p
  | r -> p ri ro
  where
  sequenceMonoidal 
    :: Proxy3 t1
    -> Proxy3 t2
    -> Proxy u1
    -> Proxy u2
    -> RLProxy rl
    -> Record r 
    -> p (et1 ri) (et2 ro)

instance emptySequenceMonoidal ::
  ( BiInvariant p
  , Unital (->) u1 u2 Unit p
  , Semigroupal (->) t1 t2 Tuple p
  , ComputeExtension t1 et1 u1
  , ComputeExtension t2 et2 u2
  ) => SequenceMonoidal t1 t2 u1 u2 et1 et2 RL.Nil r () () p
  where
  sequenceMonoidal pt1 pt2 _ _ _ _ = biinvmap (elim pt1) (contraElim pt1) (elim pt2) (contraElim pt2) (punit unit :: p u1 u2)

instance stepSequenceMonoidal ::
  ( BiInvariant p
  , Unital (->) u1 u2 Unit p
  , Semigroupal (->) t1 t2 Tuple p
  , IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , Lacks x ro'
  , Lacks x ri'
  , SequenceMonoidal t1 t2 u1 u2 et1 et2 rl r ri' ro' p
  ) => SequenceMonoidal t1 t2 u1 u2 et1 et2 (RL.Cons x (p i o) rl) r ri ro p
  where
  sequenceMonoidal pt1 pt2 pu1 pu2 _ r = biinvmap (embed k) (project k) (embed k) (project k) (pzip (Tuple (get k r) rest) :: p (t1 i (et1 ri')) (t2 o (et2 ro')))
    where
    k :: SProxy x
    k = SProxy
    rest :: p (et1 ri') (et2 ro')
    rest = sequenceMonoidal pt1 pt2 pu1 pu2 (RLProxy :: _ rl) r

sequenceMux
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Tuple Tuple Unit Unit Record Record rl r ri ro p
  => Record r
  -> p (Record ri) (Record ro)
sequenceMux r = sequenceMonoidal (Proxy3 :: _ Tuple) (Proxy3 :: _ Tuple) (Proxy :: _ Unit) (Proxy :: _ Unit) (RLProxy :: _ rl) r

sequenceDemux
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Either Either Void Void Variant Variant rl r ri ro p
  => Record r
  -> p (Variant ri) (Variant ro)
sequenceDemux r = sequenceMonoidal (Proxy3 :: _ Either) (Proxy3 :: _ Either) (Proxy :: _ Void) (Proxy :: _ Void) (RLProxy :: _ rl) r

sequenceSwitch
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Tuple Either Unit Void Record Variant rl r ri ro p
  => Record r
  -> p (Record ri) (Variant ro)
sequenceSwitch r = sequenceMonoidal (Proxy3 :: _ Tuple) (Proxy3 :: _ Either) (Proxy :: _ Unit) (Proxy :: _ Void) (RLProxy :: _ rl) r

sequenceSplice
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => SequenceMonoidal Either Tuple Void Unit Variant Record rl r ri ro p
  => Record r
  -> p (Variant ri) (Record ro)
sequenceSplice r = sequenceMonoidal (Proxy3 :: _ Either) (Proxy3 :: _ Tuple) (Proxy :: _ Void) (Proxy :: _ Unit) (RLProxy :: _ rl) r
