{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
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
module Hask.Power where

import qualified Control.Applicative as Base
import qualified Control.Arrow as Arrow
import Control.Category (Category(..))
import qualified Data.Constraint as Constraint
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

class (Profunctor (Power :: * -> j -> j), k ~ (~>)) => Powered (k :: j -> j -> *) | j -> k where
  type Power :: * -> j -> j
  -- | Power _ b -| (_ ~> b) a contravariant adjunction
  _Power :: forall (u :: *) (u' :: *) (a :: j) (a' :: j) (b :: j) (b' :: j).
             Iso (a ~> Power u b) (a' ~> Power u' b') (u -> (a ~> b)) (u' -> (a' ~> b'))

-- powers are traditionally denoted ⋔ in prefix, but ⋔ is an operator
infixr 0 ⋔
type (⋔) = Power

flip :: Powered k => (a ~> u ⋔ b) -> u -> k a b
flip = get _Power

unflip :: Powered k => (u -> k a b) -> a ~> u ⋔ b
unflip = beget _Power

instance Powered (->) where
  type Power = (->)
  _Power = dimap Prelude.flip Prelude.flip

newtype Power1 v f a = Power { runPower :: v -> f a }

instance Contravariant Power1 where
  contramap f = nat2 $ Power . lmap f . runPower

instance Functor (Power1 v) where
  fmap f = Nat $ Power . fmap1 (runNat f) . runPower

instance Semimonoidal (Power1 v) where
  ap2 = Nat $ \(Lift (Power va, Power vb)) -> Power $ \v -> Lift (va v, vb v)

instance Monoidal (Power1 v) where
  ap0 = Nat $ \(Const ()) -> Power $ \v -> Const ()

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

-- (i -> *) is powered over Hask
instance Powered (Nat :: (i -> *) -> (i -> *) -> *) where
  type Power = Power1
  _Power = dimap
     (\k v -> Nat $ \f -> runPower (runNat k f) v)
     (\k -> Nat $ \a' -> Power $ \u' -> runNat (k u') a')

-- (i -> *) is bipowered over Hask
--instance Copower1 =| Power1 where
--  curry (Nat f) = Nat $ \a -> Power $ \b -> f (Copower a b)
--  uncurry (Nat f) = Nat $ \(Copower a b) -> runPower (f a) b
