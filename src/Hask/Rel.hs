{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Hask.Rel where

import Hask.Core

-- | Rel should be a faithful functor that is also injective on objects.
--
-- and it sometimes has adjoints, if either exist, then they should satisfy the following relationship
--
-- @
-- 'Reflected' '-|' 'Rel' '-|' 'Coreflected'
-- @
--
-- This provides the inclusion functor for a subcategory with objects indexed in @i@ into a category with objects in @j@
type family Rel :: i -> j
type instance Rel = Const1
type instance Rel = Const2
type instance Rel = ConstC
type instance Rel = Id1 -- full
type instance Rel = IdC -- full
-- type instance Rel = Id2 -- full

-- | The <http://en.wikipedia.org/wiki/Reflective_subcategory "reflector"> of a
-- reflective sub-category with objects in @j@ of a category with objects in @i@.
--
-- @
-- 'Reflected' '-|' 'Rel'
-- @
type family Reflected :: j -> i
type instance Reflected = Colim1
type instance Reflected = Colim2
type instance Reflected = Id1
type instance Reflected = IdC
-- type instance Reflected = Id2

-- | This <http://en.wikipedia.org/wiki/Reflective_subcategory "coreflector"> of a coreflective sub-category with objects in @j@ of a category with objects in @i@.
--
-- @
-- 'Rel' '-|' 'Coreflected'
-- @
type family Coreflected :: j -> i
type instance Coreflected = Lim1
type instance Coreflected = Lim2
type instance Coreflected = LimC
type instance Coreflected = Id1
type instance Coreflected = IdC
-- type instance Coreflected = Id2
