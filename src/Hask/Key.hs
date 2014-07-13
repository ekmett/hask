{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Key where

import Hask.Core

ifmap :: (Functor f, Post Functor at) => (a ~> b) -> f (at i a) ~> f (at i b)
ifmap = fmap . fmap1

class (hom ~ Hom) => HasAtkey (hom :: y -> y -> *) where
  type Atkey :: x -> y -> x -> y
  atkey :: forall (a :: y) i. a ~> Atkey i a i
  atkeyFunctor1 :: Dict (Post Functor (Atkey :: x -> y -> x -> y))
  default atkeyFunctor1 :: Post Functor (Atkey :: x -> y -> x -> y) => Dict (Post Functor (Atkey :: x -> y -> x -> y))
  atkeyFunctor1 = Dict

-- Conor McBride's "Atkeykey" adapted to this formalism
data Atkey0 i a j where
  Atkey :: a -> Atkey0 i a i

instance HasAtkey (->) where
  type Atkey = Atkey0
  atkey = Atkey
  atkeyFunctor1 = Dict

instance Functor (Atkey0 i) where
  fmap f = Nat $ \(Atkey a) -> Atkey (f a)

instance Cosemimonoidal (Atkey0 i) where
  op2 = Nat $ \(Atkey eab) -> Lift (bimap Atkey Atkey eab)

instance Comonoidal (Atkey0 i) where
  op0 = Nat $ \(Atkey v) -> Const v

instance Cosemigroup m => Cosemigroup (Atkey0 i m) where
  comult = comultOp

instance Comonoid m => Comonoid (Atkey0 i m) where
  zero = zeroOp

ireturn :: (Monoidal m, Strength m) => a ~> m (Atkey0 i a) i
ireturn a = runNat return (Atkey a)

-- ibind :: Monad m => (a ~> m (Atkey k b) j) ~> m (Atkey j a) i ~> m (Atkey k b) i
--ibind :: Monad m => (a ~> m atkb j) ~> m (Atkey0 j a) i ~> m atkb i
--ibind f = bind (\(Atkey a) -> f a)

newtype Coatkey0 i a j = Coatkey { runCoatkey :: (i ~ j) => a }

class hom ~ Hom => HasCoatkey (hom :: y -> y -> *) where
  -- The dual of Conor McBride's "Atkeykey" adapted to this formalism
  type Coatkey :: x -> y -> x -> y
  coatkey :: forall (a :: y) i. Coatkey i a i ~> a
  coatkeyFunctor1 :: Dict (Post Functor (Coatkey :: x -> y -> x -> y))
  default coatkeyFunctor1 :: Post Functor (Coatkey :: x -> y -> x -> y) => Dict (Post Functor (Coatkey :: x -> y -> x -> y))
  coatkeyFunctor1 = Dict

instance Functor (Coatkey0 i) where
  fmap f = Nat $ \xs -> Coatkey $ f (runCoatkey xs)

instance Semimonoidal (Coatkey0 i) where
  ap2 = Nat $ \ab -> Coatkey $ case ab of
    Lift (Coatkey a, Coatkey b) -> (a, b)

instance Monoidal (Coatkey0 i) where
  ap0 = Nat $ \a -> Coatkey (getConst a)

instance Semigroup m => Semigroup (Coatkey0 i m) where
  mult = multM

instance Monoid m => Monoid (Coatkey0 i m) where
  one = oneM

iextract :: Comonad w => w (Coatkey0 i a) i ~> a
iextract = runCoatkey . runNat extract

-- instance Atkey0 x -| Coatkey0 x where
