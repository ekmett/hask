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
-- The definitions here are loosely based on Conor McBride's <https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf "Kleisli Arrows of Outrageous Fortune">.
--------------------------------------------------------------------
module Hask.Key where

import Hask.Core

ifmap :: (Functor f, Functor at) => (a ~> b) -> f (at a i) ~> f (at b i)
ifmap = fmap . first

class (Category hom, hom ~ Hom) => HasAtkey (hom :: y -> y -> *) where
  type Atkey :: y -> x -> x -> y
  atkey :: forall (a :: y) i. a ~> Atkey a i i
  ibind :: forall (m :: (x -> y) -> x -> y) (a :: y) (bk :: x -> y) (i :: x) (j :: x). Monad m => (a ~> m bk j) -> m (Atkey a j) i ~> m bk i
  ireturn :: (Monoidal m, Strength m) => hom a (m (Atkey a i) i)

  atkeyComonoidal :: Dict (Comonoidal (Atkey :: y -> x -> x -> y))
  default atkeyComonoidal :: Comonoidal (Atkey :: y -> x -> x -> y) => Dict (Comonoidal (Atkey :: y -> x -> x -> y))
  atkeyComonoidal = Dict

  -- The dual of Conor McBride's "Atkey" adapted to this formalism
  type Coatkey :: y -> x -> x -> y
  coatkey :: forall (a :: y) (i :: x). hom (Coatkey a i i) a

  coatkeyMonoidal :: Dict (Monoidal (Coatkey :: y -> x -> x -> y))
  default coatkeyMonoidal :: Monoidal (Coatkey :: y -> x -> x -> y) => Dict (Monoidal (Coatkey :: y -> x -> x -> y))
  coatkeyMonoidal = Dict

  iextend :: forall (w :: (x -> y) -> x -> y) (ak :: x -> y) (i :: x) (j :: x) (b :: y). Comonad w => (w ak j ~> b) -> w ak i ~> w (Coatkey b j) i

  iextract :: Comonad w => hom (w (Coatkey a i) i) a
  iextract = coatkey . runNat extract

  -- There is an adjunction between the obligations of Atkey and the problem solved by Coatkey
  atkeyAdj :: forall (a :: y) (b :: y) (a' :: y) (b' :: y) (i :: x) (j :: x) (i' :: x') (j' :: x').
    Iso (Atkey a i j ~> b) (Atkey a' i' j' ~> b')
        (a ~> Coatkey b i j)   (a' ~> Coatkey b' i' j')

-- Conor McBride's "Atkey" adapted to this formalism
data Atkey0 a i j where
  Atkey :: a -> Atkey0 a i i

newtype Coatkey0 a i j = Coatkey { runCoatkey :: (i ~ j) => a }

instance HasAtkey (->) where
  type Atkey = Atkey0
  atkey = Atkey
  ibind f = runNat (bind (Nat (\(Atkey a) -> f a)))
  ireturn a = runNat return (atkey a) -- we can't point-free this one currently in GHC, so we need it in the class
  atkeyComonoidal = Dict

  type Coatkey = Coatkey0
  coatkey = runCoatkey
  coatkeyMonoidal = Dict
  iextend f = runNat (extend (Nat (\a -> Coatkey (f a))))

  atkeyAdj = dimap (\aijb a -> Coatkey $ aijb $ Atkey a) (\abij (Atkey a) -> runCoatkey (abij a))

instance Functor Atkey0 where
  fmap f = nat2 $ \(Atkey a) -> Atkey (f a)

instance Cosemimonoidal Atkey0 where
  op2 = nat2 $ \(Atkey eab) -> Lift2 $ Lift $ bimap Atkey Atkey eab

instance Comonoidal Atkey0 where
  op0 = nat2 $ \(Atkey v) -> Const2 $ Const v

instance Cosemigroup m => Cosemigroup (Atkey0 m) where
  comult = comultOp

instance Comonoid m => Comonoid (Atkey0 m) where
  zero = zeroOp

instance Functor Coatkey0 where
  fmap f = nat2 $ \xs -> Coatkey $ f (runCoatkey xs)

instance Semimonoidal Coatkey0 where
  ap2 = nat2 $ \ab -> Coatkey $ case ab of
    Lift2 (Lift (Coatkey a, Coatkey b)) -> (a, b)

instance Monoidal Coatkey0 where
  ap0 = nat2 $ \a -> Coatkey (getConst (getConst2 a))

instance Semigroup m => Semigroup (Coatkey0 m) where
  mult = multM

instance Monoid m => Monoid (Coatkey0 m) where
  one = oneM

