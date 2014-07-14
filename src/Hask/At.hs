{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
module Hask.At where

import Hask.Core

ifmap :: (Functor f, Functor at) => (a ~> b) -> f (at a i) ~> f (at b i)
ifmap = fmap . first

class (Category hom, hom ~ Hom) => HasAt (hom :: y -> y -> *) where
  type At :: y -> x -> x -> y
  at :: forall (a :: y) i. a ~> At a i i
  ibind :: forall (m :: (x -> y) -> x -> y) (a :: y) (bk :: x -> y) (i :: x) (j :: x). Monad m => (a ~> m bk j) -> m (At a j) i ~> m bk i
  ireturn :: (Monoidal m, Strength m) => hom a (m (At a i) i)

  atComonoidal :: Dict (Comonoidal (At :: y -> x -> x -> y))
  default atComonoidal :: Comonoidal (At :: y -> x -> x -> y) => Dict (Comonoidal (At :: y -> x -> x -> y))
  atComonoidal = Dict

  -- The dual of Conor McBride's "At" adapted to this formalism
  type Coat :: y -> x -> x -> y
  coat :: forall (a :: y) (i :: x). hom (Coat a i i) a

  coatMonoidal :: Dict (Monoidal (Coat :: y -> x -> x -> y))
  default coatMonoidal :: Monoidal (Coat :: y -> x -> x -> y) => Dict (Monoidal (Coat :: y -> x -> x -> y))
  coatMonoidal = Dict

  iextend :: forall (w :: (x -> y) -> x -> y) (ak :: x -> y) (i :: x) (j :: x) (b :: y). Comonad w => (w ak j ~> b) -> w ak i ~> w (Coat b j) i

  iextract :: Comonad w => hom (w (Coat a i) i) a
  iextract = coat . runNat extract

  -- There is an adjunction between the obligations of At and the problem solved by Coat
  atAdj :: forall (a :: y) (b :: y) (a' :: y) (b' :: y) (i :: x) (j :: x) (i' :: x') (j' :: x').
    Iso (At a i j ~> b)   (At a' i' j' ~> b')
        (a ~> Coat b i j) (a' ~> Coat b' i' j')

-- Conor McBride's "At" adapted to this formalism
data At0 a i j where
  At :: a -> At0 a i i

newtype Coat0 a i j = Coat { runCoat :: (i ~ j) => a }

instance HasAt (->) where
  type At = At0
  at = At
  ibind f = runNat (bind (Nat (\(At a) -> f a)))
  ireturn a = runNat return (at a) -- we can't point-free this one currently in GHC, so we need it in the class
  atComonoidal = Dict

  type Coat = Coat0
  coat = runCoat
  coatMonoidal = Dict
  iextend f = runNat (extend (Nat (\a -> Coat (f a))))

  atAdj = dimap (\aijb a -> Coat $ aijb $ At a) (\abij (At a) -> runCoat (abij a))

instance Functor At0 where
  fmap f = nat2 $ \(At a) -> At (f a)

instance Cosemimonoidal At0 where
  op2 = nat2 $ \(At eab) -> Lift2 $ Lift $ bimap At At eab

instance Comonoidal At0 where
  op0 = nat2 $ \(At v) -> Const2 $ Const v

instance Cosemigroup m => Cosemigroup (At0 m) where
  comult = comultOp

instance Comonoid m => Comonoid (At0 m) where
  zero = zeroOp

instance Functor Coat0 where
  fmap f = nat2 $ \xs -> Coat $ f (runCoat xs)

instance Semimonoidal Coat0 where
  ap2 = nat2 $ \ab -> Coat $ case ab of
    Lift2 (Lift (Coat a, Coat b)) -> (a, b)

instance Monoidal Coat0 where
  ap0 = nat2 $ \a -> Coat (getConst (getConst2 a))

instance Semigroup m => Semigroup (Coat0 m) where
  mult = multM

instance Monoid m => Monoid (Coat0 m) where
  one = oneM

class    (a & (i~j)) => AtC a i j
instance (a & (i~j)) => AtC a i j

instance Class (a & (i ~ j)) (AtC a i j) where cls = Sub Dict
instance (a & (i~j)) :=> AtC a i j where ins = Sub Dict

class    ((i~j) |- a) => CoatC a i j
instance ((i~j) |- a) => CoatC a i j

instance Class ((i~j)|-a) (CoatC a i j) where cls = Sub Dict
instance ((i~j)|-a) :=> CoatC a i j where ins = Sub Dict

instance HasAt (:-) where
  type At = AtC
  at = Sub Dict
  ibind f = runNat $ bind $ Nat $ Sub $ Dict \\ f
  ireturn = runNat return . at
  atComonoidal = undefined -- TODO: Dict

  type Coat = CoatC
  coat = apply . fmap1 ii . beget rho . cls where
    ii :: () :- (i ~ i)
    ii = Sub Dict
  coatMonoidal = undefined -- TODO: Dict

  iextract = coat . runNat extract

  -- this was a lot harder to write than it looks!
  atAdj = dimap (\a-> ins.curry(a.ins)) (\c -> uncurry (cls.c).cls)

instance Functor AtC where
  fmap f = nat2 $ ins . first f . cls

instance Functor CoatC where
  fmap f = nat2 $ ins . fmap1 f . cls

instance Semimonoidal CoatC where
  ap2 = Nat $ Nat (ins . ap2 . bimap cls cls . get _Lift) . get _Lift
