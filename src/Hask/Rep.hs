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
import Control.Category
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

instance ( Representable p
         , Representable q
         , Composed (Compose :: (j -> i) -> (k -> j) -> k -> i)
         , Functor (Rep q)
         , Category (Hom :: i -> i -> *)
         , Category (Hom :: j -> j -> *)
         ) => Representable (Prof (p :: j -> k -> *) (q :: i -> j -> *)) where
  type Rep (Prof p q) = Compose (Rep q) (Rep p)
  _Rep = dimap (\(Prof p q) -> compose . fmap (get _Rep p) . get _Rep q)
               (\k -> Prof (beget _Rep id) (beget _Rep (decompose . k)))

{-
downs = dimap hither yon where
  hither (Prof (Down xgc) (Down dfx)) = Down (Compose . fmap xgc . dfx)
  yon (Down dfgc) = Prof (Down id) (Down (getCompose . dfgc))
-}

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

instance ( Corepresentable p
         , Corepresentable q
         , Composed (Compose :: (j -> k) -> (i -> j) -> i -> k)
         , Functor (Corep p)
         , Category (Hom :: j -> j -> *)
         , Category (Hom :: k -> k -> *)
         ) => Corepresentable (Prof (p :: j -> k -> *) (q :: i -> j -> *)) where
  type Corep (Prof p q) = Compose (Corep p) (Corep q)
  _Corep = dimap (\(Prof p q) -> get _Corep p . fmap (get _Corep q) . decompose)
                 (\k -> Prof (beget _Corep (k . compose)) (beget _Corep id))

{-
ups = dimap hither yon where
  hither (Prof (Up gxc) (Up fdx)) = Up (gxc . fmap fdx . getCompose)
  yon (Up dgfc) = Prof (Up (dgfc . Compose)) (Up id)
-}
