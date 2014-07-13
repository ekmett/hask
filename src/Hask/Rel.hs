{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Hask.Rel where

import Hask.Core

-- This provides a canonical faithful functor that is injective on objects.
type family Rel :: i -> j
type instance Rel = Const1
type instance Rel = Const2
type instance Rel = ConstC
type instance Rel = Id1 -- full
type instance Rel = IdC -- full
-- type instance Rel = Id2 -- full

-- Rel is a faithful functor
--
-- and it sometimes has adjoints, if both exist, then these should satisfy the following relationship
--
-- Reflected -| Rel -| Coreflected

type family Reflected :: j -> i
type instance Reflected = Colim1
type instance Reflected = Colim2
type instance Reflected = Id1
type instance Reflected = IdC
-- type instance Reflected = Id2

type family Coreflected :: j -> i
type instance Coreflected = Lim1
type instance Coreflected = Lim2
type instance Coreflected = LimC
type instance Coreflected = Id1
type instance Coreflected = IdC
-- type instance Coreflected = Id2
