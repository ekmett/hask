{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
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
type instance Rel = Const1        -- @* -> j -> *@
type instance Rel = Const2        -- @(i -> *) -> j -> i -> *@
type instance Rel = ConstC        -- @Constraint -> i -> Constraint@
type instance Rel = Id0           -- @* -> *@
type instance Rel = Id1           -- @(i -> *) -> i -> *@
type instance Rel = IdC           -- @i -> i@
type instance Rel = Dict
type instance Rel = No

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
type instance Reflected = Id0
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
type instance Coreflected = Id0
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

instance Id0 ~| Id0 where radj = adj.pre _Id
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

-- this should form a tensor with unit Rel
class (rel ~ Rel, Tensor (RelCompose :: (j -> c) -> (j -> c) -> j -> c)) => RelComposed (rel :: j -> c) where
  type RelCompose :: (j -> c) -> (j -> c) -> (j -> c)

  rcomposed :: Functor f' =>
     Iso (RelCompose f) (RelCompose f')
         (Compose (Lan rel f)) (Compose (Lan rel f'))

instance RelComposed Id0 where
  type RelCompose = Compose1
  rcomposed = mapping (un epsilonLan)

instance RelComposed Id1 where
  type RelCompose = Compose2
  rcomposed = mapping (un epsilonLan)

newtype ComposeConst1 (f :: * -> i -> *) (g :: * -> i -> *) (a :: *) (b :: i) = ComposeConst1 { decomposeConst1 :: Compose2 (Lan2 Const1 f) g a b }

instance Functor ComposeConst1 where
  fmap f = Nat $ dimap (nat2 decomposeConst1) (nat2 ComposeConst1) $ first $ fmap1 f

instance Functor (ComposeConst1 f) where
  fmap f = dimap (nat2 decomposeConst1) (nat2 ComposeConst1) $ Nat $ composed $ fmap2 $ runNat f

instance Functor g => Functor (ComposeConst1 f g) where
  fmap f = dimap (Nat decomposeConst1) (Nat ComposeConst1) $ composed $ fmap2 $ fmap f

instance Semitensor ComposeConst1 where
  type Tensorable ComposeConst1 = Functor
  second f = runNat (beget rcomposed) . Nat (composed (fmap2 (runNat f))) . runNat (get rcomposed)
  associate = dimap (runNat (beget rcomposed) . Nat (composed go) . runNat (get rcomposed)) undefined where
    go :: Lan2 Const1 (ComposeConst1 a b) (c x) ~> Lan2 Const1 a (ComposeConst1 b c x)
    go = Nat $ \(Lan2 l) -> Lan2 $ \a2zc -> undefined -- TODO

type instance I ComposeConst1 = Const1
instance Tensor ComposeConst1 where
  lambda = undefined
  rho = dimap (nat2 $ undefined . runNat decompose . decomposeConst1) -- TODO
              (nat2 $ \a -> ComposeConst1 $ runNat compose $ Lan2 $ \k -> runNat decompose $ runNat2 k a)


instance RelComposed Const1 where
  type RelCompose = ComposeConst1
  rcomposed = dimap (nat3 decomposeConst1) (nat3 ComposeConst1)
