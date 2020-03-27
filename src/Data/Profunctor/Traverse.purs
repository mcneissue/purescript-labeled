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
import Prim.RowList (class RowToList, kind RowList)
import Record (get)
import Type.RowList as RL
import Unsafe.Coerce (unsafeCoerce)

class 
  ( Unital (->) Void Void Unit p
  , Semigroupal (->) Either Either Tuple p
  ) <= FoldDemux (rl :: RL.RowList) (ril :: RL.RowList) (rol :: RL.RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p
  | rl -> p ril rol
  where
  foldDemuxImpl :: RLProxy rl
                -> RLProxy ril
                -> RLProxy rol 
                -> Record r 
                -> p (Variant ri) (Variant ro)

instance emptyFoldDemux :: 
  ( Unital (->) Void Void Unit p
  , Semigroupal (->) Either Either Tuple p
  ) => FoldDemux RL.Nil RL.Nil RL.Nil r ri ro p 
  where
  foldDemuxImpl _ _ _ _ = dimap unsafeCoerce absurd initial -- :S

instance stepFoldDemux ::
  ( IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , FoldDemux rl ril rol r ri ro p
  ) => FoldDemux (RL.Cons x (p i o) rl) (RL.Cons x i ril) (RL.Cons x o rol) r ri ro p
  where
  foldDemuxImpl _ _ _ r = dimap (projectE k) (injectE k) (demux (get k r) rest)
    where
    k :: SProxy x
    k = SProxy
    
    rest :: p (Variant ri) (Variant ro)
    rest = foldDemuxImpl (RLProxy :: RLProxy rl) (RLProxy :: RLProxy ril) (RLProxy :: RLProxy rol) r

foldDemux :: forall rl ril rol r ri ro p
           . RL.RowToList r rl
          => RL.RowToList ri ril
          => RL.RowToList ro rol
          => FoldDemux rl ril rol r ri ro p
          => Record r
          -> p (Variant ri) (Variant ro)
foldDemux r = foldDemuxImpl (RLProxy :: RLProxy rl) (RLProxy :: RLProxy ril) (RLProxy :: RLProxy rol) r

class 
  ( Unital (->) Unit Void Unit p
  , Semigroupal (->) Tuple Either Tuple p
  ) <= FoldSwitch (rl :: RowList) (ril :: RowList) (rol :: RowList) (r :: # Type) (ri :: # Type) (ro :: # Type) p
  | rl -> p ril rol
  where  
  foldSwitchImpl :: RLProxy rl
                 -> RLProxy ril
                 -> RLProxy rol 
                 -> Record r  
                 -> p (Record ri) (Variant ro)

instance emptyFoldSwitch :: 
  ( Unital (->) Unit Void Unit p
  , Semigroupal (->) Tuple Either Tuple p
  ) => FoldSwitch RL.Nil RL.Nil RL.Nil r ri ro p 
  where
  foldSwitchImpl _ _ _ _ = dimap (const unit) absurd poly

instance stepFoldSwitch ::
  ( IsSymbol x
  , Cons x (p i o) r' r
  , Cons x i ri' ri
  , Cons x o ro' ro
  , FoldSwitch rl ril rol r ri ro p
  ) => FoldSwitch (RL.Cons x (p i o) rl) (RL.Cons x i ril) (RL.Cons x o rol) r ri ro p
  where
  foldSwitchImpl _ _ _ r = dimap (getTR k) (injectE k) $ switch (get k r) rest
    where
    k :: SProxy x
    k = SProxy

    rest :: p (Record ri) (Variant ro)
    rest = foldSwitchImpl (RLProxy :: RLProxy rl) (RLProxy :: RLProxy ril) (RLProxy :: RLProxy rol) r

foldSwitch :: forall rl ril rol r ri ro p
            . RL.RowToList r rl
           => RowToList ri ril
           => RowToList ro rol
           => FoldSwitch rl ril rol r ri ro p
           => Record r
           -> p (Record ri) (Variant ro)
foldSwitch r = foldSwitchImpl (RLProxy :: RLProxy rl) (RLProxy :: RLProxy ril) (RLProxy :: RLProxy rol) r

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
