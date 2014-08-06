module Hask.ST where

import Hask.Core
import Control.Monad.ST
import Data.STRef

type family ST :: (* -> k) -> * -> k
type instance ST = ST0

-- ST :: (* -> *) -> * -> *
newtype ST0 f s = ST1 { runST1 :: ST s (f s) }

runST :: Lim (ST1 (Const a)) ~> Const a 
