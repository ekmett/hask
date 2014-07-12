{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Lens where

import Control.Category
import Data.Constraint
import Hask.Core
import qualified Prelude

-- todo make this a pre-req to Tensor?
class (Precartesian ((~>) :: i -> i -> *), Profunctor p) => Strong (p :: i -> i -> *) where
  {-# MINIMAL _1 | _2 #-}
  _1 :: p a b -> p (a * c) (b * c)
  _1 = dimap swap swap . _2
  _2 :: p a b -> p (c * a) (c * b)
  _2 = dimap swap swap . _1

instance Strong (->) where
  _1 = first
  _2 = fmap1

instance Strong (:-) where
  _1 = first
  _2 = fmap1

instance Strong (Nat::(i-> *)->(i-> *)-> *) where
  _1 = first
  _2 = fmap1

instance Strong (Nat::(i-> Constraint)->(i-> Constraint)-> *) where
  _1 = first
  _2 = fmap1

instance Precartesian ((~>)::i->i-> *) => Strong (Get (r::i)) where
  _1 = _Get (. fst)

-- A Freyd category over a category is an arrow
class (Strong p, Category p) => Freyd p
instance (Strong p, Category p) => Freyd p

type Getter s a = forall p. (Strong p, Post Functor p) => p a a -> p s s

-- to :: (s ~> a) -> Getter s a
to :: (Contravariant p, Post Contravariant p) => (s ~> a) -> p a a -> p s s
to f = lmap f . contramap1 f

type Lens s t a b = forall p. Strong p => p a b -> p s t

type Traversal s t a b = forall p. (Strong p, Post Monoidal p) => p a b -> p s t

-- TODO: Down f given f Monoidal is Post Monoidal
