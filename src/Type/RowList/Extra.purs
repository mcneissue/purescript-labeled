module Type.RowList.Extra where

import Prelude

import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Type.Prelude (Proxy(..))
import Type.RowList (Cons)

uncons :: ∀ k v r. Proxy (Cons k v r) -> Proxy k /\ Proxy r
uncons _ = Proxy /\ Proxy

head :: ∀ k v r. Proxy (Cons k v r) -> Proxy k
head = fst <<< uncons

tail :: ∀ k v r. Proxy (Cons k v r) -> Proxy r
tail = snd <<< uncons

