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

class (c ~ Hom) => HasRan (c :: k -> k -> *) | k -> c where
  type Ran :: (i -> j) -> (i -> k) -> j -> k
  ranDict :: Dict (Curried Compose (Ran :: (i -> j) -> (i -> k) -> j -> k))
  default ranDict :: Curried Compose (Ran :: (i -> j) -> (i -> k) -> j -> k) => Dict (Curried Compose (Ran :: (i -> j) -> (i -> k) -> j -> k))
  ranDict = Dict

data Ran1 f g a = forall z. Ran (Compose z f ~> g) (z a)

instance Curried Compose1 Ran1 where
  curry l = Nat (Ran l)
  uncurry l = Nat $ \ (Compose ab) -> case runNat l ab of
    Ran czfg za -> runNat czfg (Compose za)

instance HasRan (->) where
  type Ran = Ran1

instance Category (Hom :: j -> j -> *) => Functor (Ran1 f :: (i -> *) -> (j -> *)) where
  fmap f = Nat $ \(Ran k z) -> Ran (f . k) z

class (c ~ Hom) => HasLan (c :: k -> k -> *) | k -> c where
  type Lan :: (i -> j) -> (i -> k) -> j -> k
  lanDict :: Dict (Cocurried (Lan :: (i -> j) -> (i -> k) -> j -> k) Compose)
  default lanDict :: Cocurried (Lan :: (i -> j) -> (i -> k) -> j -> k) Compose => Dict (Cocurried (Lan :: (i -> j) -> (i -> k) -> j -> k) Compose)
  lanDict = Dict

newtype Lan1 f g a = Lan { runLan :: forall z. (g ~> Compose z f) ~> z a }

instance Cocurried Lan1 Compose1 where
  cocurry l = Nat $ \b -> Compose $ runNat l (Lan $ \f -> case runNat f b of Compose z -> z)
  uncocurry k = Nat $ \xs -> runLan xs k

instance HasLan (->) where
  type Lan = Lan1

instance Category (Hom :: j -> j -> *) => Functor (Lan1 f :: (i -> *) -> (j -> *)) where
  fmap f = Nat $ \l -> Lan $ \k -> runLan l (k . f)
