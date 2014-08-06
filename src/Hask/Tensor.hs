{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, AllowAmbiguousTypes, LambdaCase, DefaultSignatures, EmptyCase #-}
module Hask.Tensor
  ( 
  -- * Tensors
    Semitensor(..), I, Tensor'(..), Tensor
  -- * Monoids
  , Semigroup(..), Monoid'(..), Monoid
  -- * Comonoids (Opmonoids)
  , Cosemigroup(..), Comonoid'(..), Comonoid
  ) where

import Hask.Category
import Data.Void

--------------------------------------------------------------------------------
-- * Monoidal Tensors and Monoids
--------------------------------------------------------------------------------

class (Bifunctor p, Dom p ~ Dom2 p, Dom p ~ Cod2 p) => Semitensor p where
  associate :: (Ob (Dom p) a, Ob (Dom p) b, Ob (Dom p) c, Ob (Dom p) a', Ob (Dom p) b', Ob (Dom p) c')
            => Iso (Dom p) (Dom p) (->) (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))

type family I (p :: i -> i -> i) :: i

class Semitensor p => Tensor' p where
  lambda :: (Ob (Dom p) a, Ob (Dom p) a') => Iso (Dom p) (Dom p) (->) (p (I p) a) (p (I p) a') a a'
  rho    :: (Ob (Dom p) a, Ob (Dom p) a') => Iso (Dom p) (Dom p) (->) (p a (I p)) (p a' (I p)) a a'

class (Monoid' p (I p), Tensor' p) => Tensor p
instance (Monoid' p (I p), Tensor' p) => Tensor p

class Semitensor p => Semigroup p m where
  mu :: Dom p (p m m) m

class (Semigroup p m, Tensor' p) => Monoid' p m where
  eta :: NatId p -> Dom p (I p) m

class (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Monoid' p m) => Monoid p m
instance (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Monoid' p m) => Monoid p m

class Semitensor p => Cosemigroup p w where
  delta :: Dom p w (p w w)

class (Cosemigroup p w, Tensor' p) => Comonoid' p w where
  epsilon :: NatId p -> Dom p w (I p)

class (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Comonoid' p w) => Comonoid p w
instance (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Comonoid' p w) => Comonoid p w

--------------------------------------------------------------------------------
-- * (&)
--------------------------------------------------------------------------------

class (p, q) => p & q
instance (p, q) => p & q

instance Functor (&) where
  type Dom (&) = (:-)
  type Cod (&) = Nat (:-) (:-)
  fmap f = Nat $ Sub $ Dict \\ f

instance Functor ((&) a) where
  type Dom ((&) a) = (:-)
  type Cod ((&) a) = (:-)
  fmap f = Sub $ Dict \\ f

instance Semitensor (&) where
  associate = dimap (Sub Dict) (Sub Dict)

type instance I (&) = (() :: Constraint)

instance Tensor' (&) where
  lambda = dimap (Sub Dict) (Sub Dict)
  rho    = dimap (Sub Dict) (Sub Dict)

instance Semigroup (&) a where
  mu = Sub Dict

instance Monoid' (&) (() :: Constraint) where
  eta _ = Sub Dict

instance Cosemigroup (&) a where
  delta = Sub Dict

instance Comonoid' (&) a where
  epsilon _ = Sub Dict

--------------------------------------------------------------------------------
-- * (,) and ()
--------------------------------------------------------------------------------

instance Semitensor (,) where
  associate = dimap (\((a,b),c) -> (a,(b,c))) (\(a,(b,c)) -> ((a,b),c))

type instance I (,) = ()

instance Tensor' (,) where
  lambda = dimap (\ ~(_,a) -> a) ((,)())
  rho    = dimap (\ ~(a,_) -> a) (\a -> (a,()))

instance Semigroup (,) () where
  mu ((),()) = ()

instance Monoid' (,) () where
  eta _ = id

instance Cosemigroup (,) a where
  delta a = (a,a)

instance Comonoid' (,) a where
  epsilon _ _ = ()

--------------------------------------------------------------------------------
-- * Either and Void
--------------------------------------------------------------------------------

instance Semitensor Either where
  associate = dimap hither yon where
    hither (Left (Left a))  = Left a
    hither (Left (Right b)) = Right (Left b)
    hither (Right c)        = Right (Right c)
    yon (Left a)            = Left (Left a)
    yon (Right (Left b))    = Left (Right b)
    yon (Right (Right c))   = Right c

type instance I Either = Void

instance Tensor' Either where
  lambda = dimap (\(Right a) -> a) Right
  rho = dimap (\(Left a) -> a) Left

instance Semigroup (,) Void where
  mu (a,_) = a

instance Semigroup Either Void where
  mu (Left a)  = a
  mu (Right b) = b

instance Monoid' Either Void where
  eta _ = absurd

instance Cosemigroup Either Void  where
  delta = absurd

instance Comonoid' Either Void where
  epsilon _ = id
