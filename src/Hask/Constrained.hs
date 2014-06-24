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
-- Copyright :  (c) Edward Kmett 2014 and Sjoerd Visscher
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- This package explores category theory via a couple of non-standard
-- tricks.
--
-- First, we use lens-style isomorphism-families to talk about
-- most operations.
--
-- Second, we heavily abuse parametricity as a proxy for naturality.
-- This means that the category Nat that gets used throughout is a
-- particularly well-behaved. An inhabitant of @Nat :: (i -> j) -> (i -> j) -> *@
-- is required to be polymorphic in its argument.
--
-- Parametricity is a very strong notion of naturality. Notably, we
-- don't have to care if i or j are co -or- contravariant. (forall a. f a ~> g a)
-- respects _both_.
--
-- Third, we use kind-indexing to pick the category. This means it
-- is harder to talk about Kleisli categories, etc. but in exchange
-- most of the category selection _just works_. A central working
-- hypothesis of this code is that this is sufficient to talk about
-- interesting categories, and it certainly results in less verbose
-- code than more explicit encodings which clutter up every type class
-- talking about the choice of category.
--
-- Here, much of the time the selection is implicit.
--------------------------------------------------------------------
module Hask.Constrained where

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

infixr |=

-- |
-- @(|=) :: Constraint -> * -> *@

-- This is a corepresentable functor
newtype p |= q = Constrained { runConstrained :: p => q }

instance Contravariant (|=) where
  contramap ab = Nat $ \bc -> Constrained $ case ab of
    Sub Dict -> runConstrained bc

instance Functor ((|=) e) where
  fmap bc ab = Constrained $ bc (runConstrained ab)

instance Semimonoidal ((|=) e) where
  ap2 (ea,eb) = Constrained $ (runConstrained ea, runConstrained eb)

instance Monoidal ((|=) e) where
  ap0 () = Constrained ()

instance Semimonad ((|=) e) where
  join cc = Constrained (runConstrained (runConstrained cc))

instance Semigroup p => Semigroup (e |= p) where
  mult = multM

instance Monoid p => Monoid (e |= p) where
  one = oneM

instance Cosemimonad ((|=) e) where
  duplicate cc = Constrained cc

instance Monoid e => Comonad ((|=) e) where
  extract cc = runConstrained cc \\ (one :: () :- e)

-- we can make an indexed adjunction for this
instance Corepresentable (|=) where
  type Corep (|=) = Dict
  _Corep = dimap (\ab Dict -> case ab of Constrained b -> b) (\ab -> Constrained $ ab Dict)

data EnvC p q = EnvC (Dict p) q

-- EnvC p (Either a b) -> Either (EnvC p a) (EnvC p b)

instance Functor EnvC where
  fmap f = Nat $ \(EnvC p q) -> EnvC (fmap f p) q

instance Functor (EnvC p) where
  fmap f (EnvC p q) = EnvC p (f q)

instance Cosemimonad (EnvC p) where
  duplicate q@(EnvC p _) = EnvC p q

instance Comonad (EnvC p) where
  extract (EnvC _ q) = q

instance Cosemimonoidal (EnvC p) where
  op2 (EnvC p eab) = bimap (EnvC p) (EnvC p) eab

instance Comonoidal (EnvC p) where
  op0 (EnvC _ v) = v

-- all constraints are semimonoids
instance Semimonoidal (EnvC p) where
  ap2 (EnvC Dict p, EnvC Dict q) = EnvC Dict (p, q)

instance Monoid p => Monoidal (EnvC p) where
  ap0 = EnvC (Dict \\ (one :: () :- p))

instance Semimonad (EnvC p) where
  join (EnvC Dict p) = p

instance EnvC =| (|=) where
  adj1 = dimap (\eab a -> Constrained $ eab (EnvC Dict a))
               (\aeb (EnvC Dict a) -> runConstrained (aeb a))

instance EnvC e -| (|=) e where
  adj = adj1
