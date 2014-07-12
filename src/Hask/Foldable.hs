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
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wall -fno-warn-missing-signatures #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Foldable where

import qualified Control.Applicative as Base
import qualified Data.Foldable as Base
import qualified Data.Functor as Base
import qualified Data.Monoid as Base
import qualified Data.Traversable as Base
import Hask.Core

-- * A kind-indexed family of categories

-- * Folding and Traversing

newtype WrapMonoid m = WrapMonoid { runWrapMonoid :: m }

instance Monoid m => Base.Monoid (WrapMonoid m) where
  mempty = WrapMonoid (one ())
  mappend (WrapMonoid a) (WrapMonoid b) = WrapMonoid (mult (a, b))

newtype WrapMonoidal f a = WrapMonoidal { runWrapMonoidal :: f a }
_WrapMonoidal = dimap runWrapMonoidal WrapMonoidal

instance Functor f => Base.Functor (WrapMonoidal f) where
  fmap f (WrapMonoidal m) = WrapMonoidal (fmap f m)

instance Monoidal f => Base.Applicative (WrapMonoidal f) where
  pure a = WrapMonoidal (return a)
  WrapMonoidal f <*> WrapMonoidal g = WrapMonoidal $ ap f g

class Functor f => Foldable f where
  foldMap :: Monoid m => (a ~> m) ~> f a ~> m

foldMapHask :: (Base.Foldable f, Monoid m) => (a -> m) -> f a -> m
foldMapHask f = runWrapMonoid . Base.foldMap (WrapMonoid . f)

class Functor f => Traversable f where
  traverse :: Monoidal m => (a ~> m b) ~> f a ~> m (f b)

fmapDefault f    = get _Id . traverse (beget _Id . f)
foldMapDefault f = get _Const . traverse (beget _Const . f)

traverseHask :: (Base.Traversable f, Monoidal m) => (a -> m b) -> f a -> m (f b)
traverseHask f = runWrapMonoidal . Base.traverse (WrapMonoidal . f)

instance Foldable [] where foldMap = foldMapHask
instance Traversable [] where traverse = traverseHask

instance Foldable Maybe where foldMap = foldMapHask
instance Traversable Maybe where traverse = traverseHask

instance Foldable (Either a) where foldMap = foldMapHask
instance Traversable (Either a) where traverse = traverseHask

-- products
instance Foldable ((,) e) where foldMap = foldMapHask
instance Traversable ((,) e) where traverse = traverseHask

instance Foldable ((&) e) where foldMap f = f . snd
instance Foldable (Lift1 (,) e) where foldMap f = f . snd
instance Foldable (Lift2 (Lift1 (,)) e) where foldMap f = f . snd

-- coproducts
instance Foldable (Lift1 Either e) where
  foldMap f = Nat $ \case
    Lift (Left _)  -> runNat one (Const ())
    Lift (Right b) -> runNat f b

instance Foldable (Lift2 (Lift1 Either) e) where
  foldMap f = Nat $ Nat $ \case
    Lift2 (Lift (Left _))  -> runNat2 one (Const2 (Const ()))
    Lift2 (Lift (Right b)) -> runNat2 f b
