module Data.Profunctor.Traverse where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Profunctor (dimap)
import Data.Profunctor.Monoidal (class Semigroupal, class Unital, demux, initial, poly, switch)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..))
import Data.Variant (Variant, inj, prj)
import Data.Variant.Internal (RLProxy(..))
import Prim.Row (class Cons)
import Prim.RowList as RL
import Record (get)
import Unsafe.Coerce (unsafeCoerce)

class 
  ( Unital (->) Void Void Unit p
  , Semigroupal (->) Either Either Tuple p
  ) <= FoldDemux (xs :: RL.RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p 
  where
  foldDemuxImpl ::  RLProxy xs -> Record r -> p (Variant ri) (Variant ro)

instance emptyFoldDemux :: 
  ( Unital (->) Void Void Unit p
  , Semigroupal (->) Either Either Tuple p
  ) => FoldDemux RL.Nil r ri ro p 
  where
  foldDemuxImpl _ _ = dimap unsafeCoerce absurd initial -- :S

instance stepFoldDemux ::
  ( IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , FoldDemux xs r ri ro p
  ) => FoldDemux (RL.Cons x (p i o) xs) r ri ro p
  where
  foldDemuxImpl _ r = dimap (projectE k) (injectE k) $ demux (get k r) rest
    where
    k :: SProxy x
    k = SProxy
    
    rest :: p (Variant ri) (Variant ro)
    rest = foldDemuxImpl (RLProxy :: RLProxy xs) r

foldDemux :: forall r ri ro xs p
           . RL.RowToList r xs
          => FoldDemux xs r ri ro p
          => Record r
          -> p (Variant ri) (Variant ro)
foldDemux = foldDemuxImpl (RLProxy :: RLProxy xs)

class 
  ( Unital (->) Unit Void Unit p
  , Semigroupal (->) Tuple Either Tuple p
  ) <= FoldSwitch (xs :: RL.RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p
  where  
  foldSwitchImpl :: RLProxy xs -> Record r -> p (Record ri) (Variant ro)

instance emptyFoldSwitch :: 
  ( Unital (->) Unit Void Unit p
  , Semigroupal (->) Tuple Either Tuple p
  ) => FoldSwitch RL.Nil r ri ro p 
  where
  foldSwitchImpl _ _ = dimap (const unit) absurd poly

instance stepFoldSwitch ::
  ( IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , FoldSwitch xs r ri ro p
  ) => FoldSwitch (RL.Cons x (p i o) xs) r ri ro p
  where
  foldSwitchImpl _ r = dimap (getTR k) (injectE k) $ switch (get k r) rest
    where
    k :: SProxy x
    k = SProxy

    rest :: p (Record ri) (Variant ro)
    rest = foldSwitchImpl (RLProxy :: RLProxy xs) r

foldSwitch :: forall r ri ro xs p
            . RL.RowToList r xs
           => FoldSwitch xs r ri ro p
           => Record r
           -> p (Record ri) (Variant ro)
foldSwitch = foldSwitchImpl (RLProxy :: RLProxy xs)

projectE :: forall s i r' r. IsSymbol s => Cons s i r' r => SProxy s -> Variant r -> Either i (Variant r)
projectE l v = case prj l v of
  Just i -> Left i
  Nothing -> Right v

injectE :: forall s o r' r. IsSymbol s => Cons s o r' r => SProxy s -> Either o (Variant r) -> Variant r
injectE l e = case e of
  Left o -> inj l o
  Right v -> v

getTR :: forall s i r' r. IsSymbol s => Cons s i r' r => SProxy s -> Record r -> Tuple i (Record r)
getTR s r = Tuple (get s r) r