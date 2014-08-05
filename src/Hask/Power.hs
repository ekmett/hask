{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wall #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Power where

import Hask.Core
import Hask.Rel
import Hask.Rep
import qualified Prelude

infixr 0 ⋔
type (⋔) = Power

class (Category ((~>) :: i -> i -> *), hom ~ Hom) => Powered (hom :: j -> j -> i) where
  type Power :: i -> j -> j
  flipped :: forall (a :: j) (u :: i) (b :: j) (a' :: j) (u' :: i) (b' :: j).
    Iso (hom a (Power u b)) (hom a' (Power u' b')) (u `Hom` hom a b) (u' `Hom` hom a' b')

flip :: Powered hom => hom a (Power u b) ~> Hom u (hom a b)
flip = get flipped

unflip :: Powered hom => Hom u (hom a b) ~> hom a (Power u b)
unflip = beget flipped

-- flippedInternal :: forall (a :: i) (u :: i) (b :: i). CCC (Hom :: i -> i -> *) => Iso' ((b^u)^a) ((b^a)^u)
--flippedInternal = dimap (curry $ curry $ apply . first apply . associate (fmap1 swap))
--                        (curry $ curry $ apply . first apply . associate (fmap1 swap))

instance Powered (->) where
  type Power = (->)
  flipped = dimap Prelude.flip Prelude.flip

instance Powered (|-) where
  type Power = (|-)
  flipped = dimap (curry $ curry $ apply . first apply . associate (fmap1 swap))
                  (curry $ curry $ apply . first apply . associate (fmap1 swap))

instance Powered (Lift1 (->)) where
  type Power = Lift (->)
  flipped = dimap (curry $ curry $ apply . first apply . associate (fmap1 swap))
                  (curry $ curry $ apply . first apply . associate (fmap1 swap))
  --flipped = dimap (Nat $ beget _Lift . fmap1 (beget _Lift) . flip . fmap1 (get _Lift) . get _Lift)
  --                (Nat $ beget _Lift . fmap1 (beget _Lift) . flip . fmap1 (get _Lift) . get _Lift)

instance Powered (Lift2 (Lift1 (->))) where
  type Power = Lift (Lift (->))
  flipped = dimap (curry $ curry $ apply . first apply . associate (fmap1 swap))
                  (curry $ curry $ apply . first apply . associate (fmap1 swap))
  --flipped = dimap (Nat $ beget _Lift . Nat (beget _Lift . fmap1 (transport (beget _Lift) . beget _Lift) . flip . fmap1 (get _Lift . transport (get _Lift)) . get _Lift) . get _Lift)
  --                (Nat $ beget _Lift . Nat (beget _Lift . fmap1 (transport (beget _Lift) . beget _Lift) . flip . fmap1 (get _Lift . transport (get _Lift)) . get _Lift) . get _Lift)

-- Power1 :: * -> (i -> *) -> (i -> *)
newtype Power1 v f a = Power { runPower :: v -> f a }

instance Powered (Nat :: (i -> *) -> (i -> *) -> *) where
  type Power = Power1
  flipped = dimap
     (\k v -> Nat $ \f -> runPower (transport k f) v)
     (\k -> Nat $ \a' -> Power $ \u' -> transport (k u') a')

instance Contravariant Power1 where
  contramap f = nat2 $ Power . lmap f . runPower

instance Functor (Power1 v) where
  fmap f = Nat $ Power . fmap1 (transport f) . runPower

instance Semimonoidal (Power1 v) where
  ap2 = Nat $ \(Lift (Power va, Power vb)) -> Power $ \v -> Lift (va v, vb v)

instance Monoidal (Power1 v) where
  ap0 = Nat $ \(Const ()) -> Power $ \_ -> Const ()

instance Semigroup m => Semigroup (Power1 v m) where
  mult = multM

instance Monoid m => Monoid (Power1 v m) where
  one = oneM

instance Semimonoidal f => Semimonoidal (Power1 v f) where
  ap2 (Power vfa, Power vfb) = Power $ \v -> ap2 (vfa v, vfb v)

instance Monoidal f => Monoidal (Power1 v f) where
  ap0 () = Power $ \_ -> ap0 ()

instance (Semimonoidal f, Semigroup m) => Semigroup (Power1 v f m) where
  mult = multM

instance (Monoidal f, Monoid m) => Monoid (Power1 v f m) where
  one = oneM

instance Functor f => Functor (Power1 v f) where
  fmap f = Power . fmap1 (fmap f) . runPower

instance Corepresentable Power1 where
  type Corep Power1 = Rel
  _Corep = dimap (Nat $ \(Power ab) -> Lift (ab . get _Const))
                 (Nat $ \(Lift ab) -> Power (ab . beget _Const))
