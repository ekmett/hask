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

class (Category hom, hom ~ Hom) => HasAtkey (hom :: y -> y -> *) where
  type Atkey :: x -> y -> x -> y
  atkey :: forall (a :: y) i. a ~> Atkey i a i
  atkeyFunctor1 :: Dict (Post Functor (Atkey :: x -> y -> x -> y))
  default atkeyFunctor1 :: Post Functor (Atkey :: x -> y -> x -> y) => Dict (Post Functor (Atkey :: x -> y -> x -> y))
  atkeyFunctor1 = Dict

  -- ibind :: Monad m => (a ~> m (Atkey k b) j) ~> m (Atkey j a) i ~> m (Atkey k b) i
  ibind :: forall (m :: (x -> y) -> x -> y) (a :: y) (kb :: x -> y) (i :: x) (j :: x). Monad m => (a ~> m kb j) -> m (Atkey j a) i ~> m kb i
  ireturn :: (Monoidal m, Strength m) => hom a (m (Atkey i a) i)

-- Conor McBride's "Atkeykey" adapted to this formalism
data Atkey0 i a j where
  Atkey :: a -> Atkey0 i a i

instance HasAtkey (->) where
  type Atkey = Atkey0
  atkey = Atkey
  atkeyFunctor1 = Dict
  ibind f = runNat (bind (Nat (\(Atkey a) -> f a)))
  ireturn a = runNat return (atkey a) -- we can't point-free this one currently in GHC, so we need it in the class

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

class (Category hom, hom ~ Hom) => HasCoatkey (hom :: y -> y -> *) where
  -- The dual of Conor McBride's "Atkeykey" adapted to this formalism
  type Coatkey :: x -> y -> x -> y
  coatkey :: forall (a :: y) (i :: x). hom (Coatkey i a i) a

  coatkeyFunctor1 :: Dict (Post Functor (Coatkey :: x -> y -> x -> y))
  default coatkeyFunctor1 :: Post Functor (Coatkey :: x -> y -> x -> y) => Dict (Post Functor (Coatkey :: x -> y -> x -> y))
  coatkeyFunctor1 = Dict

  iextend :: forall (w :: (x -> y) -> x -> y) (ka :: x -> y) (i :: x) (j :: x) (b :: y). Comonad w => (w ka j ~> b) -> w ka i ~> w (Coatkey j b) i

  iextract :: Comonad w => hom (w (Coatkey i a) i) a
  iextract = coatkey . runNat extract

newtype Coatkey0 i a j = Coatkey { runCoatkey :: (i ~ j) => a }

instance HasCoatkey (->) where
  type Coatkey = Coatkey0
  coatkey = runCoatkey
  coatkeyFunctor1 = Dict
  iextend f = runNat (extend (Nat (\a -> Coatkey (f a))))

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

-- atkeyAdj :: Iso' (Atkey i a j ~> b) (a ~> Coatkey i b j) -- if we shuffle the args we can make this a normal adjunction in Nat x -> y -> z
