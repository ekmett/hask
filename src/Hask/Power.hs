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

-- * Work in progress

-- | Copower e -| (~>) e
--
-- note this is forced to be on the 'wrong side' like products in Haskell.
type family Copower :: x -> y -> x

type instance Copower = (,)
type instance Copower = Copower1
type instance Copower = Copower2_1
type instance Copower = Copower2

-- Nat :: (i -> *) -> (i -> *) -> * is tensored. (Copowered over Hask)
data Copower1 f x a = Copower (f a) x

instance Functor Copower1 where
  fmap (Nat f) = nat2 $ \(Copower fa x) -> Copower (f fa) x

instance Functor (Copower1 f) where
  fmap f = Nat $ \(Copower fa x) -> Copower fa (f x)

instance Functor f => Functor  (Copower1 f a) where
  fmap f (Copower fa x) = Copower (fmap f fa) x

instance Contravariant f => Contravariant (Copower1 f a) where
  contramap f (Copower fa x) = Copower (contramap f fa) x

instance Copower1 =| Nat where
  adj1 = dimap (\(Nat f) a -> Nat $ \e -> f (Copower e a))
              (\f -> Nat $ \(Copower e a) -> runNat (f a) e)

instance Copower1 e -| Nat e where
  adj = adj1

-- Nat :: (i -> j -> *) -> (i -> j -> *) -> * is tensored. (Copowered over Hask)
data Copower2 f x a b = Copower2 (f a b) x

instance Functor Copower2 where
  fmap f = nat3 $ \(Copower2 fab x) -> Copower2 (runNat2 f fab) x

instance Functor (Copower2 f) where
  fmap f = nat2 $ \(Copower2 fab x) -> Copower2 fab (f x)

instance Functor f => Functor (Copower2 f x) where
  fmap f = Nat $ \(Copower2 fa x) -> Copower2 (first f fa) x

instance Contravariant f => Contravariant (Copower2 f x) where
  contramap f = Nat $ \(Copower2 fa x) -> Copower2 (lmap f fa) x

instance Post Functor f => Functor (Copower2 f x a) where
  fmap f (Copower2 fab x) = Copower2 (fmap1 f fab) x

instance Post Contravariant f => Contravariant (Copower2 f x a) where
  contramap f (Copower2 fab x) = Copower2 (contramap1 f fab) x

instance Copower2 =| Nat where
  adj1 = dimap (\f a -> nat2 $ \e -> runNat (runNat f) (Copower2 e a))
              (\f -> nat2 $ \(Copower2 e a) -> runNat2 (f a) e)

instance Copower2 e -| Nat e where
  adj = adj1

-- Nat :: (i -> j -> *) -> (i -> j -> *) -> * is tensored. (Copowered over Nat :: (i -> *) -> (i -> *) -> *)
data Copower2_1 f x a b = Copower2_1 (f a b) (x a)

instance Functor Copower2_1 where
  fmap f = nat3 $ \(Copower2_1 fab x) -> Copower2_1 (runNat2 f fab) x

instance Functor (Copower2_1 f) where
  fmap f = nat2 $ \(Copower2_1 fab x) -> Copower2_1 fab (runNat f x)

instance (Functor f, Functor x) => Functor (Copower2_1 f x) where
  fmap f = Nat $ \(Copower2_1 fa x) -> Copower2_1 (first f fa) (fmap f x)

instance (Contravariant f, Contravariant x) => Contravariant (Copower2_1 f x) where
  contramap f = Nat $ \(Copower2_1 fa x) -> Copower2_1 (lmap f fa) (contramap f x)

instance Post Functor f => Functor (Copower2_1 f x a) where
  fmap f (Copower2_1 fab x) = Copower2_1 (fmap1 f fab) x

instance Post Contravariant f => Contravariant (Copower2_1 f x a) where
  contramap f (Copower2_1 fab x) = Copower2_1 (contramap1 f fab) x

instance Copower2_1 =| Lift1 Nat where
  adj1 = dimap (\f -> Nat $ \a -> Lift $ Nat $ \e -> runNat2 f (Copower2_1 e a))
               (\f -> nat2 $ \(Copower2_1 e a) -> runNat (lower (runNat f a)) e)

instance Copower2_1 e -| Lift1 Nat e where
  adj = adj1

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
unflip = unget _Power

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
instance Curried Copower1 Power1 where
  curry (Nat f) = Nat $ \a -> Power $ \b -> f (Copower a b)
  uncurry (Nat f) = Nat $ \(Copower a b) -> runPower (f a) b
