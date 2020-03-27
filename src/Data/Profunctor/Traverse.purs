module Data.Profunctor.Traverse where

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
  ( Unital (->) u1 u2 Unit p
  , Semigroupal (->) t1 t2 Tuple p
  , ComputeExtension t1 et1 u1
  , ComputeExtension t2 et2 u2
  ) <= FoldMonoidal t1 t2 u1 u2 et1 et2 (rl :: RL.RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p
  | r -> p ri ro
  where
  foldMonoidalImpl 
    :: Proxy3 t1
    -> Proxy3 t2
    -> Proxy u1
    -> Proxy u2
    -> RLProxy rl
    -> Record r 
    -> p (et1 ri) (et2 ro)

instance emptyFoldMonoidal ::
  ( Unital (->) u1 u2 Unit p
  , Semigroupal (->) t1 t2 Tuple p
  , ComputeExtension t1 et1 u1
  , ComputeExtension t2 et2 u2
  ) => FoldMonoidal t1 t2 u1 u2 et1 et2 RL.Nil r () () p
  where
  foldMonoidalImpl pt1 pt2 _ _ _ _ = dimap (contraElim pt1) (elim pt2) (punit unit :: p u1 u2)

instance stepFoldMonoidal ::
  ( IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , Lacks x ro'
  , Lacks x ri'
  , FoldMonoidal t1 t2 u1 u2 et1 et2 rl r ri' ro' p
  ) => FoldMonoidal t1 t2 u1 u2 et1 et2 (RL.Cons x (p i o) rl) r ri ro p
  where
  foldMonoidalImpl pt1 pt2 pu1 pu2 _ r = dimap (project k) (embed k) (pzip (Tuple (get k r) rest) :: p (t1 i (et1 ri')) (t2 o (et2 ro')))
    where
    k :: SProxy x
    k = SProxy
    rest :: p (et1 ri') (et2 ro')
    rest = foldMonoidalImpl pt1 pt2 pu1 pu2 (RLProxy :: RLProxy rl) r

foldMux
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => FoldMonoidal Tuple Tuple Unit Unit Record Record rl r ri ro p
  => Record r
  -> p (Record ri) (Record ro)
foldMux r = foldMonoidalImpl (Proxy3 :: Proxy3 Tuple) (Proxy3 :: Proxy3 Tuple) (Proxy :: Proxy Unit) (Proxy :: Proxy Unit) (RLProxy :: RLProxy rl) r

foldDemux
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => FoldMonoidal Either Either Void Void Variant Variant rl r ri ro p
  => Record r
  -> p (Variant ri) (Variant ro)
foldDemux r = foldMonoidalImpl (Proxy3 :: Proxy3 Either) (Proxy3 :: Proxy3 Either) (Proxy :: Proxy Void) (Proxy :: Proxy Void) (RLProxy :: RLProxy rl) r

foldSwitch
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => FoldMonoidal Tuple Either Unit Void Record Variant rl r ri ro p
  => Record r
  -> p (Record ri) (Variant ro)
foldSwitch r = foldMonoidalImpl (Proxy3 :: Proxy3 Tuple) (Proxy3 :: Proxy3 Either) (Proxy :: Proxy Unit) (Proxy :: Proxy Void) (RLProxy :: RLProxy rl) r

foldSplice
  :: forall r rl ri ro p
   . RL.RowToList r rl
  => FoldMonoidal Either Tuple Void Unit Variant Record rl r ri ro p
  => Record r
  -> p (Variant ri) (Record ro)
foldSplice r = foldMonoidalImpl (Proxy3 :: Proxy3 Either) (Proxy3 :: Proxy3 Tuple) (Proxy :: Proxy Void) (Proxy :: Proxy Unit) (RLProxy :: RLProxy rl) r