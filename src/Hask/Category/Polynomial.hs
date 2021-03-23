{-# LANGUAGE RankNTypes, PolyKinds, DataKinds, ConstraintKinds, ScopedTypeVariables, KindSignatures, TypeFamilies, MultiParamTypeClasses, UndecidableInstances, UndecidableSuperClasses, GADTs, AllowAmbiguousTypes, FlexibleInstances, NoImplicitPrelude #-}
module Hask.Category.Polynomial
  (
  -- * Product Category
    Product(..), ProductOb, Fst, Snd
  -- * Coproduct Category
  , Coproduct(..), CoproductOb(..)
  -- * Unit Category
  , Unit(..)
  -- * Empty Category
  , Empty
  , Void, absurd

  ) where

import Hask.Category
import Data.Void
import Hask.Functor.Faithful

--------------------------------------------------------------------------------
-- * Products
--------------------------------------------------------------------------------

-- TODO: do this as a product of profunctors instead?
data Product (p :: i -> i -> *) (q :: j -> j -> *) (a :: (i, j)) (b :: (i, j)) =
  Product (p (Fst a) (Fst b)) (q (Snd a) (Snd b))

type family Fst (p :: (i,j)) :: i
type instance Fst '(a,b) = a

type family Snd (q :: (i,j)) :: j
type instance Snd '(a,b) = b

class    (Ob p (Fst a), Ob q (Snd a)) => ProductOb (p :: i -> i -> *) (q :: j -> j -> *) (a :: (i,j))
instance (Ob p (Fst a), Ob q (Snd a)) => ProductOb (p :: i -> i -> *) (q :: j -> j -> *) (a :: (i,j))

instance (Category p, Category q) => Functor (Product p q) where
  type Dom (Product p q) = Op (Product (Opd p) (Opd q))
  type Cod (Product p q) = Nat (Product (Dom2 p) (Dom2 q)) (->)
  fmap f = case observe f of
    Dict -> Nat (. unop f)

instance (Category p, Category q, ProductOb p q a) => Functor (Product p q a) where
  type Dom (Product p q a) = Product (Dom2 p) (Dom2 q)
  type Cod (Product p q a) = (->)
  fmap = (.)

instance (Category p, Category q) => Category' (Product p q) where
  type Ob (Product p q) = ProductOb p q
  id = Product id id
  Product f f' . Product g g' = Product (f . g) (f' . g')
  observe (Product f g) = case observe f of
    Dict -> case observe g of
      Dict -> Dict


--------------------------------------------------------------------------------
-- * Coproducts
--------------------------------------------------------------------------------

data Coproduct (c :: i -> i -> *) (d :: j -> j -> *) (a :: Either i j) (b :: Either i j) where
  Inl :: c x y -> Coproduct c d ('Left x) ('Left y)
  Inr :: d x y -> Coproduct c d ('Right x) ('Right y)

class CoproductOb (p :: i -> i -> *) (q :: j -> j -> *) (a :: Either i j) where
  side :: Endo (Coproduct p q) a -> (forall x. (a ~ 'Left x, Ob p x) => r) -> (forall y. (a ~ 'Right y, Ob q y) => r) -> r
  coproductId :: Endo (Coproduct p q) a

instance (Category p, Ob p x) => CoproductOb (p :: i -> i -> *) (q :: j -> j -> *) ('Left x :: Either i j) where
  side _ r _ = r
  coproductId = Inl id

instance (Category q, Ob q y) => CoproductOb (p :: i -> i -> *) (q :: j -> j -> *) ('Right y :: Either i j) where
  side _ _ r = r
  coproductId = Inr id

instance (Category p, Category q) => Functor (Coproduct p q) where
  type Dom (Coproduct p q) = Op (Coproduct p q)
  type Cod (Coproduct p q) = Nat (Coproduct p q) (->)
  fmap (Op f) = Nat (. f)

instance (Category p, Category q) => Functor (Coproduct p q a) where
  type Dom (Coproduct p q a) = Coproduct p q
  type Cod (Coproduct p q a) = (->)
  fmap = (.)

instance (Category p, Category q) => Category' (Coproduct p q) where
  type Ob (Coproduct p q) = CoproductOb p q
  id = coproductId
  observe (Inl f) = case observe f of
    Dict -> Dict
  observe (Inr f) = case observe f of
    Dict -> Dict
  Inl f . Inl g = Inl (f . g)
  Inr f . Inr g = Inr (f . g)

--------------------------------------------------------------------------------
-- * The Unit category
--------------------------------------------------------------------------------

data Unit a b = Unit

instance Functor Unit where
  type Dom Unit = Op Unit
  type Cod Unit = Nat Unit (->)
  fmap _ = Nat $ \_ -> Unit

instance Functor (Unit a) where
  type Dom (Unit a) = Unit
  type Cod (Unit a) = (->)
  fmap _ _ = Unit

instance Category' Unit where
  type Ob Unit = Vacuous Unit
  id = Unit
  Unit . Unit = Unit
  observe _ = Dict

instance FullyFaithful Unit where
  unfmap _ = Op Unit

instance FullyFaithful (Unit a) where
  unfmap _ = Unit


--------------------------------------------------------------------------------
-- * The Empty category
--------------------------------------------------------------------------------

data Empty (a :: Void) (b :: Void)

{-
instance Functor Empty where
  type Dom Empty = Op Empty
  type Cod Empty = Nat Empty (->)
  fmap f = case f of {}

instance No (:-) a => Functor (Empty a) where
  type Dom (Empty a) = Empty
  type Cod (Empty a) = (->)
  fmap f = case f of {}

data NO = No

-- | the functor from the empty category to every category
type No = (Any 'No :: (i -> i -> *) -> Void -> i)

-- | the empty category
instance Category' c => Functor (No c) where
  type Dom (No c) = Empty
  type Cod (No c) = c
  fmap f = case f of {}

instance Category' Empty where
  type Ob Empty = No (:-)
  id = undefined -- no
  f . _ = case f of {}
  observe f = case f of {}
-}
