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
import Hask.Power

-- * Foldable

class Functor f => Foldable (f :: i -> j) where
  foldMap :: Monoid m => (a ⋔ m) ~> m^f a

newtype WrapMonoid m = WrapMonoid { runWrapMonoid :: m }

instance Monoid m => Base.Monoid (WrapMonoid m) where
  mempty = WrapMonoid (one ())
  mappend (WrapMonoid a) (WrapMonoid b) = WrapMonoid (mult (a, b))

foldMapHask :: (Base.Foldable f, Monoid m) => (a -> m) -> f a -> m
foldMapHask f = runWrapMonoid . Base.foldMap (WrapMonoid . f)

instance Foldable [] where foldMap = foldMapHask
instance Foldable Maybe where foldMap = foldMapHask

instance Foldable (,) where
  foldMap = Nat $ \f -> Lift $ runPower f . fst
instance Foldable ((,) e) where foldMap = lmap snd

instance Foldable Either where
  foldMap = Nat $ \f -> Lift $ (runPower f ||| \ _ -> runNat one (Const ()))

instance Foldable (Either a) where foldMap = foldMapHask

instance Foldable ((&) e) where foldMap = lmap snd

-- TODO: instance Foldable (Lift1 (,))
instance Foldable (Lift1 (,) e) where foldMap = lmap snd
-- TODO: instance Foldable (Lift2 (Lift1 (,)))
instance Foldable (Lift2 (Lift1 (,)) e) where foldMap = lmap snd

-- TODO: instance Foldable (Lift1 Either)
instance Foldable (Lift1 Either e) where
  foldMap = Nat $ \ f -> Lift $ \case
    Lift (Left _)  -> runNat one (Const ())
    Lift (Right e) -> lower f e

-- TODO: instance Foldable (Lift2 (Lift1 Either))
instance Foldable (Lift2 (Lift1 Either) e) where
  foldMap = nat2 $ \ (Lift2 (Lift f)) -> Lift2 $ Lift $ \case
    Lift2 (Lift (Left _))  -> runNat2 one (Const2 (Const ()))
    Lift2 (Lift (Right e)) -> f e

-- TODO: instance Foldable Compose1 -- we don't have sufficient Power levels

-- * Traversable

class Functor f => Traversable f where
  -- (Rel a ~> m b) -> f a ~> m (f b) ?
  traverse :: Monoidal m => (a ~> m b) -> f a ~> m (f b)

newtype WrapMonoidal f a = WrapMonoidal { runWrapMonoidal :: f a }
_WrapMonoidal = dimap runWrapMonoidal WrapMonoidal

instance Functor f => Base.Functor (WrapMonoidal f) where
  fmap f (WrapMonoidal m) = WrapMonoidal (fmap f m)

instance Monoidal f => Base.Applicative (WrapMonoidal f) where
  pure a = WrapMonoidal (return a)
  WrapMonoidal f <*> WrapMonoidal g = WrapMonoidal $ ap f g

fmapDefault f    = get _Id . traverse (beget _Id . f)
foldMapDefault f = get _Const . traverse (beget _Const . f)

traverseHask :: (Base.Traversable f, Monoidal m) => (a -> m b) -> f a -> m (f b)
traverseHask f = runWrapMonoidal . Base.traverse (WrapMonoidal . f)

instance Traversable [] where traverse = traverseHask

instance Traversable Maybe where traverse = traverseHask

instance Traversable (Either a) where traverse = traverseHask

instance Traversable ((,) e) where traverse = traverseHask
