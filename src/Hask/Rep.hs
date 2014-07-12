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
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Rep where

import Data.Constraint
import Hask.Core
import Hask.Prof
import qualified Prelude

-- * Representability

class Representable (p :: x -> y -> *) where
  type Rep p :: y -> x
  _Rep :: Iso (p a b) (p a' b') (a ~> Rep p b) (a' ~> Rep p b')

instance Representable (->) where
  type Rep (->) = Id
  _Rep = un (mapping _Id)

instance Representable (Nat :: (i -> *) -> (i -> *) -> *) where
  type Rep (Nat :: (i -> *) -> (i -> *) -> *) = Id
  _Rep = un (mapping _Id)

instance Representable (:-) where
  type Rep (:-) = Id
  _Rep = un (mapping _Id)

instance Representable (Down f) where
  type Rep (Down f) = f
  _Rep = dimap runDown Down

-- instance (Representable p, Representable q) => Representable (Prof p q :: i -> j -> *) where
--  type Rep (Prof p q) = Up (Rep q) (Rep p)

class Corepresentable (p :: x -> y -> *) where
  type Corep p :: x -> y
  _Corep :: Iso (p a b) (p a' b') (Corep p a ~> b) (Corep p a' ~> b')

instance Corepresentable (->) where
  type Corep (->) = Id
  _Corep = lmapping _Id

instance Corepresentable (Nat :: (i -> *) -> (i -> *) -> *) where
  type Corep (Nat :: (i -> *) -> (i -> *) -> *) = Id
  _Corep = lmapping _Id

instance Corepresentable (:-) where
  type Corep (:-) = Id
  _Corep = lmapping _Id

instance Corepresentable (Up f) where
  type Corep (Up f) = f
  _Corep = dimap runUp Up
