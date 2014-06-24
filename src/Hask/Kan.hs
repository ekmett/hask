{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Kan where

import qualified Control.Applicative as Base
import qualified Control.Arrow as Arrow
import Control.Category (Category(..))
import qualified Data.Constraint as Constraint
import Data.Constraint ((:-)(Sub), (\\), Dict(Dict))
import qualified Data.Foldable as Base
import qualified Data.Functor as Base
import qualified Data.Functor.Identity as Base
import qualified Data.Monoid as Base
import Data.Proxy
import Data.Tagged
import qualified Data.Traversable as Base
import Data.Void
import Hask.Core
import Hask.Power
import qualified Prelude
import Prelude (Either(..), ($), either, Bool, undefined, Maybe(..))
import GHC.Exts (Constraint, Any)
import Unsafe.Coerce (unsafeCoerce)

-- Lan g -| Up g -| Ran g
type family Lan  :: (i -> j) -> (i -> k) -> j -> k
type family Ran  :: (i -> j) -> (i -> k) -> j -> k

type instance Ran = Ran0
newtype Ran0 (f :: i -> j) (g :: i -> *) (a :: j) = Ran { runRan :: forall r. (a ~> f r) ⋔ g r }

-- instance Up1 g -| Ran1 g

-- alternately, by universal property
-- data Ran f g a = forall z. Functor z => Ran (forall x. z (f x) ~> g x) (z a)

instance Category ((~>) :: j -> j -> *) => Contravariant (Ran0 :: (i -> j) -> (i -> *) -> j -> *) where
  contramap (Nat f) = nat2 $ \(Ran k) -> Ran $ k . (f .)

instance Category (Cod f) => Functor (Ran0 f) where
  fmap (Nat f) = Nat $ \(Ran k) -> Ran $ f . k

type instance Ran = Ran1
newtype Ran1 f g a x = Ran1 { runRan2 :: forall r. ((a ~> f r) ⋔ g r) x }

type instance Lan = Lan0
data Lan0 f g a where
  Lan :: Copower (g b) (f b ~> a) -> Lan0 f g a

type instance Lan = Lan1
data Lan1 f g a x where
  Lan1 :: Copower (g b) (f b ~> a) x -> Lan1 f g a x

-- newtype Codensity f a = Codensity { runCodensity :: forall r. f r^a ~> f r }
-- newtype Yoneda f a = Yoneda { runYoneda :: forall r. r^a ~> f r }
