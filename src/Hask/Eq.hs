{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Hask.Eq where

import Data.Type.Equality ((:~:)(..))
import Hask.Core

type family (==) :: i -> i -> j
type instance (==) = (~)   -- @k -> k -> Constraint@
type instance (==) = (:~:) -- @k -> k -> *@

class hom ~ Hom => Subst (hom :: j -> j -> k) where
  subst :: Hom (a == b) (hom (f a) (f b))

instance Subst (:-) where
  subst Refl = id

instance Subst (->) where
  subst Refl = id

instance Subst (|-) where
  subst = go where
    go :: forall f a b. (a == b) :- (f a |- f b)
    go = Sub $ Dict \\ (jot :: () :- f a |- f a)
