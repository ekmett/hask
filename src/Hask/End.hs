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
module Hask.End where

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
import qualified Prelude
import Prelude (Either(..), ($), either, Bool, undefined, Maybe(..))
import GHC.Exts (Constraint, Any)
import Unsafe.Coerce (unsafeCoerce)

-- * Ends

type family End :: (i -> i -> j) -> j

newtype End1 f = End { getEnd :: forall x. f x x }
type instance End = End1

instance Functor End1 where
  fmap f (End fcc) = End $ runNat2 f fcc

newtype End2 f y = End2 { getEnd2 :: forall x. f x x y }
type instance End = End2

instance Functor End2 where
  fmap f = Nat $ \(End2 fcc) -> End2 $ runNat3 f fcc

newtype End3 f y z = End3 { getEnd3 :: forall x. f x x y z }
type instance End = End3

instance Functor End3 where
  fmap f = nat2 $ \(End3 fcc) -> End3 $ runNat4 f fcc

-- assumes p is contravariant in its first argument, covariant in its second
class EndC (p :: i -> i -> Constraint) where
  endDict :: Dict (p a a)

type instance End = EndC

instance p Any Any => EndC (p :: i -> i -> Constraint) where
  endDict = case unsafeCoerce (id :: p Any Any :- p Any Any) :: p Any Any :- p a a of
    Sub d -> d

instance Functor EndC where
  fmap f = dimap (Sub endDict) (Sub Dict) (runAny f) where
    runAny :: (p ~> q) -> p Any Any ~> q Any Any
    runAny = runNat2

-- * Coends

type family Coend :: (i -> i -> j) -> j

data Coend1 f where
  Coend :: f x x -> Coend1 f

type instance Coend = Coend1

instance Functor Coend1 where
  fmap f (Coend fcc) = Coend $ runNat2 f fcc

data Coend2 f y where
  Coend2 :: f x x y -> Coend2 f y

type instance Coend = Coend2

instance Functor Coend2 where
  fmap f = Nat $ \(Coend2 fcc) -> Coend2 $ runNat3 f fcc
