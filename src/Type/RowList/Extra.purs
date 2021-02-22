module Type.RowList.Extra where

import Prelude

import Data.Symbol (SProxy(..))
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Type.RowList (RLProxy(..), Cons)

uncons :: ∀ k v r. RLProxy (Cons k v r) -> SProxy k /\ RLProxy r
uncons _ = SProxy /\ RLProxy

head :: ∀ k v r. RLProxy (Cons k v r) -> SProxy k
head = fst <<< uncons

tail :: ∀ k v r. RLProxy (Cons k v r) -> RLProxy r
tail = snd <<< uncons

