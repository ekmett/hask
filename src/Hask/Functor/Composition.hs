{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, AllowAmbiguousTypes, LambdaCase, DefaultSignatures, EmptyCase #-}
module Hask.Functor.Composition where

import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import GHC.Prim (Any)
import Hask.Category
import Hask.Iso
import Hask.Tensor
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- * Compose
--------------------------------------------------------------------------------

data COMPOSE = Compose
type Compose = (Any 'Compose :: (i -> i -> *) -> (j -> j -> *) -> (k -> k -> *) -> (j -> k) -> (i -> j) -> i -> k)

class Category e => Composed (e :: k -> k -> *) where
  _Compose :: (FunctorOf d e f, FunctorOf d e f', FunctorOf c d g, FunctorOf c d g') => Iso
    e e (->)
    (Compose c d e f g a) (Compose c d e f' g' a')
    (f (g a))             (f' (g' a'))

instance Composed (->) where
  _Compose = unsafeCoerce

instance Composed (:-) where
  _Compose = unsafeCoerce

instance (Category c, Composed d) => Composed (Nat c d) where
  _Compose = unsafeCoerce -- really evil, like super-villain evil

instance (Category c, Category d, Category e) => Class (f (g a)) (Compose c d e f g a) where cls = unsafeCoerceConstraint
instance (Category c, Category d, Category e) => f (g a) :=> Compose c d e f g a where ins = unsafeCoerceConstraint

instance (Category c, Category d, Composed e) => Functor (Compose c d e) where
  type Dom (Compose c d e) = Nat d e
  type Cod (Compose c d e) = Nat (Nat c d) (Nat c e)
  fmap = fmap' where
    fmap' :: Nat d e a b -> Nat (Nat c d) (Nat c e) (Compose c d e a) (Compose c d e b)
    fmap' n@Nat{} = nat $ \g -> nat $ \a -> _Compose $ n ! g ! a

instance (Category c, Category d, Composed e, Functor f, e ~ Cod f, d ~ Dom f) => Functor (Compose c d e f) where
  type Dom (Compose c d e f) = Nat c d
  type Cod (Compose c d e f) = Nat c e
  fmap (Nat f) = Nat $ _Compose $ fmap f

instance (Category c, Category d, Composed e, Functor f, Functor g, e ~ Cod f, d ~ Cod g, d ~ Dom f, c ~ Dom g) => Functor (Compose c d e f g) where
  type Dom (Compose c d e f g) = c
  type Cod (Compose c d e f g) = e
  fmap f = _Compose $ fmap $ fmap f

instance (Composed c, c ~ c', c' ~ c'') => Semitensor (Compose c c' c'' :: (i -> i) -> (i -> i) -> (i -> i)) where
  associate = associateCompose

data ID = Id
type Id = (Any 'Id :: (i -> i -> *) -> i -> i)

class Category c => Identified (c :: i -> i -> *) where
  _Id :: Iso c c (->) (Id c a) (Id c a') a a'

instance Identified (->) where
  _Id = unsafeCoerce

instance Identified (:-) where
  _Id = unsafeCoerce

instance (Category c, Identified d) => Identified (Nat c d) where
  _Id = unsafeCoerce

instance Category c => Class a (Id c a) where cls = unsafeCoerceConstraint
instance Category c => a :=> Id c a where ins = unsafeCoerceConstraint

instance Identified c => Functor (Id c) where
  type Dom (Id c) = c
  type Cod (Id c) = c
  fmap = _Id

type instance I (Compose c c c) = Id c

instance (Identified c, Composed c) => Semigroup (Compose c c c) (Id c) where
  mu = dimap (get lambda) id id

instance (Identified c, Composed c) => Monoid' (Compose c c c) (Id c) where
  eta _ = Nat $ _Id id

instance (Identified c, Composed c) => Cosemigroup (Compose c c c) (Id c) where
  delta = dimap id (beget lambda) id

instance (Identified c, Composed c) => Comonoid' (Compose c c c) (Id c) where
  epsilon _ = Nat $ _Id id

instance (Identified c, Composed c) => Tensor' (Compose c c c :: (i -> i) -> (i -> i) -> (i -> i)) where
  lambda = lambdaCompose
  rho = rhoCompose

associateCompose :: forall b c d e f g h f' g' h'.
   ( Category b, Category c, Composed d, Composed e
   , FunctorOf d e f, FunctorOf c d g, FunctorOf b c h
   , FunctorOf d e f', FunctorOf c d g', FunctorOf b c h'
   ) => Iso (Nat b e) (Nat b e) (->)
  (Compose b c e (Compose c d e f g) h) (Compose b c e (Compose c d e f' g') h')
  (Compose b d e f (Compose b c d g h)) (Compose b d e f' (Compose b c d g' h'))
associateCompose = dimap hither yon where
  hither = nat $ \a -> case obOf (id :: NatId f) $ (id :: NatId g) ! (id :: NatId h) ! a of
    Dict -> case obOf (id :: NatId f) $ (id :: NatId (Compose b c d g h)) ! a of
      Dict -> case obOf (id :: NatId (Compose c d e f g)) $ (id :: NatId h) ! a of
        Dict -> beget _Compose . fmap (beget _Compose) . get _Compose . get _Compose
  yon = nat $ \a -> case obOf (id :: NatId f') $ (id :: NatId g') ! (id :: NatId h') ! a of
    Dict -> case obOf (id :: NatId f') $ (id :: NatId (Compose b c d g' h')) ! a of
      Dict -> case obOf (id :: NatId (Compose c d e f' g')) $ (id :: NatId h') ! a of
        Dict -> beget _Compose . beget _Compose . fmap (get _Compose) . get _Compose

lambdaCompose :: forall a a' c. (Identified c, Composed c, Ob (Nat c c) a, Ob (Nat c c) a')
              => Iso (Nat c c) (Nat c c) (->) (Compose c c c (Id c) a) (Compose c c c (Id c) a') a a'
lambdaCompose = dimap hither yon where
  hither = nat $ \z -> case obOf (id :: NatId (Id c)) $ (id :: NatId a) ! z of
    Dict -> get _Id . get _Compose
  yon = nat $ \z -> case obOf (id :: NatId (Id c)) $ (id :: NatId a') ! z of
    Dict -> beget _Compose . beget _Id

rhoCompose :: forall a a' c. (Identified c, Composed c, Ob (Nat c c) a, Ob (Nat c c) a')
           => Iso (Nat c c) (Nat c c) (->) (Compose c c c a (Id c)) (Compose c c c a' (Id c)) a a'
rhoCompose = dimap hither yon where
  hither = nat $ \z -> case obOf (id :: NatId a) $ (id :: NatId (Id c)) ! z of
    Dict -> fmap (get _Id) . get _Compose
  yon = nat $ \z -> case obOf (id :: NatId a') $ (id :: NatId (Id c)) ! z of
    Dict -> beget _Compose . fmap (beget _Id)

--------------------------------------------------------------------------------
-- ** Monads
--------------------------------------------------------------------------------

class (Functor m, Dom m ~ Cod m, Monoid (Compose (Dom m) (Dom m) (Dom m)) m, Identified (Dom m), Composed (Dom m)) => Monad m where
  return :: Ob (Dom m) a => Dom m a (m a)
  return = runNat (eta (id :: NatId (Compose (Dom m) (Dom m) (Dom m)))) . beget _Id
  bind :: forall a b. Ob (Dom m) b => Dom m a (m b) -> Dom m (m a) (m b)
  bind f = case observe f of
    Dict -> case obOf (id :: NatId m) (id :: Endo (Cod m) (m b)) of
      Dict -> runNat mu . beget _Compose . fmap f
instance (Functor m, Dom m ~ Cod m, Monoid (Compose (Dom m) (Dom m) (Dom m)) m, Identified (Dom m), Composed (Dom m)) => Monad m
