{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, RankNTypes, TypeOperators, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances, GADTs, UndecidableInstances #-}

import GHC.Prim (Any)
import Unsafe.Coerce (unsafeCoerce)
import Prelude (undefined, ($))

type family (~>) :: i -> i -> *
type instance (~>) = (->)

newtype Nat f g = Nat { runNat :: forall a. f a ~> g a }
type instance (~>) = Nat

class Functor (f :: i -> j) where
  fmap :: (a ~> b) -> f a ~> f b

-- Either a :: * -> *
instance Functor (Either a) where
  fmap f = \case
    Left a -> Left a
    Right a -> Right (f a)

-- Either :: * -> (* -> *)
instance Functor Either where
  fmap f = Nat $ \case
    Left a -> Left (f a)
    Right a -> Right a

class Profunctor p where
  dimap :: (a ~> b) -> (c ~> d) -> p b c ~> p a d

class (Profunctor p, p ~ (~>)) => Category p where
  id   :: p a a
  (.)  :: p b c -> p a b -> p a c
  evil :: p a b
  evil = unsafeCoerce (id :: p a a)

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

data COMPOSE = Compose
type Compose = (Any 'Compose :: (j -> k) -> (i -> j) -> i -> k)

composed :: Category ((~>) :: k -> k -> *) => Iso (Compose f g a :: k) (Compose f' g' a' :: k) (f (g a)) (f' (g' a))
composed = dimap evil evil

data Prod (p :: (i,j)) (q :: (i,j)) where
  Prod :: (a ~> b) -> (c ~> d) -> Prod '(a,c) '(b,d)

type instance (~>) = Prod -- :: (i,j) -> (i,j) -> *)

class Functor f where
  fmap :: (a ~> b) -> f a ~> f b

instance Category ((~>) :: j -> j -> *) => Functor ('(,) :: i -> j -> (i, j)) where
  fmap f = Nat $ Prod f id

instance Category ((~>) :: i -> i -> *) => Functor ('(,) a :: j -> (i, j)) where
  fmap = Prod id

-- '(,) 1 2 :: (Nat, Nat)

{-
instance Functor ('Left :: a -> Either a b)
instance Functor ('Right :: b -> Either a b)
instance Functor ('Just :: a -> Maybe a)
-}

data LIM = Lim
type Lim = (Any 'Lim :: (i -> j) -> j)

data CONST = Const
type Const = (Any 'Const :: j -> i -> j)

class f -| g | f -> g, g -> f where
  adj :: Iso (f a ~> b) (f a' ~> b') (a ~> g b) (a' ~> g b')

instance Const -| Lim where
  adj = dimap todo todo

todo :: a
todo = undefined

newtype Get r a b = Get { runGet :: a ~> r }
