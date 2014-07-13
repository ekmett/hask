{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Hask.Rel where

import Hask.Core
import Data.Functor.Identity as Base

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
type instance Rel = Const1        -- @* -> j -> *@
type instance Rel = Const2        -- @(i -> *) -> j -> i -> *@
type instance Rel = ConstC        -- @Constraint -> i -> Constraint@
type instance Rel = Base.Identity -- @* -> *@
type instance Rel = Id1           -- @(i - *) -> i -> *@
type instance Rel = IdC           -- @i -> i@
-- type instance Rel = Id2

-- | The <http://en.wikipedia.org/wiki/Reflective_subcategory "reflector"> of a
-- reflective sub-category with objects in @j@ of a category with objects in @i@.
--
-- @
-- 'Reflected' '-|' 'Rel'
-- @
type family Reflected :: j -> i
type instance Reflected = Colim1
type instance Reflected = Colim2
type instance Reflected = Base.Identity
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
type instance Coreflected = Base.Identity
type instance Coreflected = Id1
type instance Coreflected = IdC
-- type instance Coreflected = Id2

-- | Relative adjoints
class (f :: j -> i) ~| (u :: i -> k) | f k -> u, u j -> f where
  -- |
  --
  -- When Rel = Identity, a relative adjunction is just a normal adjunction, and you can use:
  --
  -- @
  -- radj = adj.pre _Id
  -- @
  radj :: Iso (f a ~> b) (f a' ~> b') (Rel a ~> u b) (Rel a' ~> u b')

instance Base.Identity ~| Base.Identity where radj = adj.pre _Id
instance Id1 ~| Id1 where radj = adj.pre _Id
instance IdC ~| IdC where radj = adj.pre _Id
instance Const1 ~| Lim1 where radj = adj.pre _Id
instance Const2 ~| Lim2 where radj = adj.pre _Id
instance ConstC ~| LimC where radj = adj.pre _Id
instance (Colim1 :: (i -> *) -> *) ~| (Const1 :: * -> i -> *) where radj = adj.pre _Id
-- instance (Colim2 :: (i -> j -> *) -> j -> *) ~| (Const2 :: (j -> *) -> i -> j -> *) where radj = adj.pre _Id


-- | Relative monads
class Functor m => RelMonad (m :: j -> c) where
  runit :: Rel a ~> m a
  rbind :: (Rel a ~> m b) -> m a ~> m b

instance RelMonad Id1 where
  runit = id
  rbind = id

instance RelMonad IdC where
  runit = id
  rbind = id

instance RelMonad Const1 where
  runit = id
  rbind = id

instance RelMonad Const2 where
  runit = id
  rbind = id

instance RelMonad ConstC where
  runit = id
  rbind = id

class rel ~ Rel => RelComposed (rel :: j -> c) where
  type RelCompose :: (j -> c) -> (j -> c) -> (j -> c)

  rcompose :: Cocurryable RelCompose f' => Iso (RelCompose f g) (RelCompose f' g') (Compose (Lan rel f) g) (Compose (Lan rel f') g')

instance RelComposed Base.Identity where
  type RelCompose = Compose1
  rcompose = firstly (un epsilonLan)
