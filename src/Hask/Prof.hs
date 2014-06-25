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
module Hask.Prof where

import Control.Category
import Hask.Core
import qualified Prelude
import Prelude (($), undefined)

-- forward profunctor composition forms a weak category.
data Prof :: (i -> j -> *) -> (j -> k -> *) -> i -> k -> * where
  Prof :: p a b -> q b c -> Prof p q a c

instance Category ((~>) :: i -> i -> *) => Semitensor (Prof :: (i -> i -> *) -> (i -> i -> *) -> i -> i -> *) where
  associate = associateProf

instance Functor Prof where
  fmap f = nat3 $ \(Prof p q) -> Prof (runNat2 f p) q

instance Functor (Prof p) where
  fmap f = nat2 $ \(Prof p q) -> Prof p (runNat2 f q)

instance Contravariant p => Contravariant (Prof p q) where
  contramap f = Nat $ \(Prof p q) -> Prof (runNat (contramap f) p) q

instance Post Functor q => Functor (Prof p q a) where
  fmap f (Prof p q) = Prof p (fmap1 f q)

associateProf :: Iso (Prof (Prof p q) r) (Prof (Prof p' q') r')
                     (Prof p (Prof q r)) (Prof p' (Prof q' r'))
associateProf = dimap
  (nat2 $ \ (Prof (Prof a b) c) -> Prof a (Prof b c))
  (nat2 $ \ (Prof a (Prof b c)) -> Prof (Prof a b) c)

{-
lambdaProf :: (Contravariant p, Category q, q ~> (~>) => Prof q p ~> p
lambdaProf = nat2 $ \(Prof h p) -> lmap h p

rhoProf :: (Category q, q ~ (~>)) => p ~> Prof p q
rhoProf = nat2 $ \p -> Prof p id
-}

newtype ProfR p q a b = ProfR { runProfR :: forall x. p x a -> q x b }

-- ProfL? =| Prof =| ProfR

instance Contravariant ProfR where
  contramap f = nat3 $ \(ProfR pq) -> ProfR $ \p -> pq (runNat2 f p)

instance Functor (ProfR p) where
  fmap f = nat2 $ \(ProfR pq) -> ProfR $ \p -> runNat2 f (pq p)

instance Post Functor p => Contravariant (ProfR p q) where
  contramap f = Nat $ \(ProfR pq) -> ProfR $ \p -> pq (fmap1 f p)

instance Post Functor q => Functor (ProfR p q a) where
  fmap f (ProfR pq) = ProfR $ \p -> fmap1 f (pq p)

instance Post Contravariant p => Functor (ProfR p q) where
  fmap f = Nat $ \(ProfR pq) -> ProfR $ \p -> pq (contramap1 f p)

instance Post Contravariant q => Contravariant (ProfR p q a) where
  contramap f (ProfR pq) = ProfR $ \p -> contramap1 f (pq p)

type instance I ProfR = (~>)

iotaProf :: (Category p, p ~ (~>), Contravariant q') => Iso (ProfR p q) (ProfR (~>) q') q q'
iotaProf = dimap (nat2 $ \(ProfR f) -> f id) (nat2 $ \f -> ProfR $ \p -> lmap p f)

jotProf :: Post Functor p => (~>) ~> ProfR p p
jotProf = nat2 $ \f -> ProfR (fmap1 f)

{-
instance InternalHom ProfR where -- requires constraints on objects of a category
  iota = iotaProf
  jot  = jotProf
-}

instance Prof =| ProfR where
   adj1 = dimap (\k -> nat2 $ \p -> ProfR $ \q -> runNat2 k (Prof q p))
                (\a2eb -> nat2 $ \(Prof e a) -> runProfR (runNat2 a2eb a) e)

instance Prof e -| ProfR e where
  adj = adj1

-- Cat^op -> Prof, Corepresentable, conjoint
data Up f a b = Up { runUp :: f a ~> b }

-- Cat -> Prof, Representable, companion
data Down f a b = Down { runDown :: a ~> f b }
