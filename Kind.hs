{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
module Group where

import Data.Void
import qualified Control.Arrow as Arrow
import qualified Prelude
import Prelude (Either(..), ($), either)

class Hom ~ h => Category (h :: i -> i -> *) | i -> h where
  type Hom :: i -> i -> *
  id  :: forall (a :: i). Hom a a
  (.) :: forall (a :: i) (b :: i) (c :: i). Hom b c -> Hom a b -> Hom a c

instance Category (->) where
  type Hom = (->)
  id x = x
  (.) f g x = f (g x)

newtype f ~> g = Nat { runNat :: forall a. f a -> g a }

instance Category (~>) where
  type Hom = (~>)
  id = Nat id
  Nat f . Nat g = Nat (f . g)

class (Category (Hom :: x -> x -> *), Category (Hom :: y -> y -> *)) => Functor (f :: x -> y) where
  fmap :: Hom a b -> Hom (f a) (f b)

instance Prelude.Functor f => Functor f where
  fmap = Prelude.fmap

instance Functor ((~>) f) where
  fmap = (.)

newtype At (x :: i) (f :: i -> *) = At { getAt :: f x }
_At = dimap getAt At

instance Functor (At x) where
  fmap (Nat f) = _At f

newtype Const (b :: *) (a :: i) = Const { getConst :: b }
_Const = dimap getConst Const

instance Functor Const where
  fmap f = Nat (_Const f)

newtype Lift (p :: * -> * -> *) (f :: i -> *) (g :: i -> *) (a :: i) = Lift { lower :: p (f a) (g a) }
_Lift = dimap lower Lift

class (Category (Hom :: x -> x -> *), Category (Hom :: z -> z -> *)) => PFunctor (p :: x -> y -> z) where
  first :: Hom a b -> Hom (p a c) (p b c)

instance PFunctor (,) where first = Arrow.first
instance PFunctor Either where first = Arrow.left
instance PFunctor p => PFunctor (Lift p) where
  first (Nat f) = Nat (_Lift $ first f)

class (Category (Hom :: y -> y -> *), Category (Hom :: z -> z -> *)) => QFunctor (p :: x -> y -> z) where
  second :: Hom a b -> Hom (p c a) (p c b)

instance QFunctor (->) where second = (.)
instance QFunctor (~>) where second = (.)
instance QFunctor (,) where second = Arrow.second
instance QFunctor Either where second = Arrow.right
instance Category (Hom :: i -> i -> *) => QFunctor (Const :: * -> i -> *) where second _ = _Const id
instance QFunctor p => QFunctor (Lift p) where
  second (Nat f) = Nat (_Lift $ second f)
instance QFunctor At where
  second (Nat f) = _At f

class (Category (Hom :: x -> x -> *), Category (Hom :: z -> z -> *)) => PContravariant (p :: x -> y -> z) where
  lmap :: Hom a b -> Hom (p b c) (p a c)

instance PContravariant (->) where lmap f g = g . f
instance PContravariant (~>) where lmap f g = g . f

class (Category (Hom :: y -> y -> *), Category (Hom :: z -> z -> *)) => QContravariant (p :: x -> y -> z) where
  qmap :: Hom a b -> Hom (p c b) (p c a)

instance Category (Hom :: i -> i -> *) => QContravariant (Const :: * -> i -> *) where qmap _ = _Const id

class (PFunctor p, QFunctor p) => Bifunctor (p :: x -> y -> z)
instance (PFunctor p, QFunctor p) => Bifunctor (p :: x -> y -> z)

class (PContravariant p, QFunctor p) => Profunctor (p :: x -> y -> z)
instance (PContravariant p, QFunctor p) => Profunctor (p :: x -> y -> z)

class (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)
instance (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)

class (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)
instance (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)

bimap :: Bifunctor p => Hom a b -> Hom c d -> Hom (p a c) (p b d)
bimap f g = first f . second g

dimap :: Profunctor p => Hom a b -> Hom c d -> Hom (p b c) (p a d)
dimap f g = lmap f . second g

rmap :: QFunctor p => Hom a b -> Hom (p c a) (p c b)
rmap = second

-- tensor for a skew monoidal category
class Bifunctor p => Tensor (p :: x -> x -> x) where
  type Id p :: x
  associate :: Hom (p (p a b) c) (p a (p b c))
  lambda    :: Hom (p (Id p) a) a
  rho       :: Hom a (p a (Id p))

instance Tensor (,) where
  type Id (,) = ()
  associate ((a,b),c) = (a,(b,c))
  lambda    ((),a)    = a
  rho       a         = (a ,())

instance Tensor Either where
  type Id Either = Void
  associate (Left (Left a)) = Left a
  associate (Left (Right b)) = Right (Left b)
  associate (Right c) = Right (Right c)
  lambda (Right a) = a
  rho = Left

instance Tensor p => Tensor (Lift p) where
  type Id (Lift p) = Const (Id p)
  associate = Nat $ _Lift $ second Lift . associate . first lower
  lambda    = Nat $ lmap (first getConst . lower) lambda
  rho       = Nat $ rmap (Lift . second Const) rho

-- symmetric monoidal category
class Bifunctor p => Symmetric p where
  swap :: Hom (p a b) (p b a)

instance Symmetric (,) where
  swap (a,b) = (b, a)

instance Symmetric Either where
  swap = either Right Left

instance Symmetric p => Symmetric (Lift p) where
  swap = Nat $ _Lift swap

-- profunctor composition
data Prof :: (j -> k -> *) -> (i -> j -> *) -> i -> k -> * where
  Prof :: forall (p :: j -> k -> *) (q :: i -> j -> *) (a :: i) (b :: j) (c :: k). p b c -> q a b -> Prof p q a c

associateProf :: forall (p :: k -> l -> *) (q :: j -> k -> *) (r :: i -> j -> *) (a :: i) (c :: l). Prof (Prof p q) r a c -> Prof p (Prof q r) a c
associateProf (Prof (Prof a b) c) = Prof a (Prof b c)

lambdaProf :: forall (p :: i -> j -> *) (a :: i) (b :: j). QFunctor p => Prof Hom p a b -> p a b
lambdaProf (Prof h p) = rmap h p

rhoProf :: forall (p :: i -> k -> *) (a :: i) (b :: k). Category (Hom :: i -> i -> *) => p a b -> Prof p Hom a b
rhoProf p = Prof p id
