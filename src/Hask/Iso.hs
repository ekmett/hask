{-# LANGUAGE NoImplicitPrelude, KindSignatures, PolyKinds, ConstraintKinds, TypeFamilies, UndecidableInstances, DataKinds, ScopedTypeVariables, RankNTypes, AllowAmbiguousTypes, FlexibleContexts #-}
module Hask.Iso
  ( 
  -- * Iso
    Iso
  -- * Get
  , Get, _Get, get
  -- * Beget
  , Beget, _Beget, beget, (#)
  -- * Yoneda 
  , yoneda
  ) where

import Hask.Category

--------------------------------------------------------------------------------
-- *  Iso
--------------------------------------------------------------------------------

type Iso c d e s t a b = forall p. (Bifunctor p, Opd p ~ c, Dom2 p ~ d, Cod2 p ~ e) => p a b -> p s t

--------------------------------------------------------------------------------
-- *  Get (Lens)
--------------------------------------------------------------------------------

newtype Get (c :: i -> i -> *) (r :: i) (a :: i) (b :: i) = Get { runGet :: c a r }

_Get :: Iso (->) (->) (->) (Get c r a b) (Get c r' a' b') (c a r) (c a' r')
_Get = dimap runGet Get

instance Category c => Functor (Get c) where
  type Dom (Get c) = c
  type Cod (Get c) = Nat (Op c) (Nat c (->))
  fmap = fmap' where
    fmap' :: c a b -> Nat (Op c) (Nat c (->)) (Get c a) (Get c b)
    fmap' f = case observe f of
      Dict -> Nat $ Nat $ _Get (f .)

instance (Category c, Ob c r) => Functor (Get c r) where
  type Dom (Get c r) = Op c
  type Cod (Get c r) = Nat c (->)
  fmap f = case observe f of
    Dict -> Nat $ _Get $ (. unop f)

instance (Category c, Ob c r, Ob c a) => Functor (Get c r a) where
  type Dom (Get c r a) = c
  type Cod (Get c r a) = (->)
  fmap _ = _Get id

get :: (Category c, Ob c a) => (Get c a a a -> Get c a s s) -> c s a
get l = runGet $ l (Get id)

--------------------------------------------------------------------------------
-- * Beget (Lens)
--------------------------------------------------------------------------------

newtype Beget (c :: i -> i -> *) (r :: i) (a :: i) (b :: i) = Beget { runBeget :: c r b }

_Beget :: Iso (->) (->) (->) (Beget c r a b) (Beget c r' a' b') (c r b) (c r' b')
_Beget = dimap runBeget Beget

instance Category c => Functor (Beget c) where
  type Dom (Beget c) = Op c
  type Cod (Beget c) = Nat (Op c) (Nat c (->))
  fmap = fmap' where
    fmap' :: Op c a b -> Nat (Op c) (Nat c (->)) (Beget c a) (Beget c b)
    fmap' f = case observe f of
      Dict -> Nat $ Nat $ _Beget (. op f)

instance (Category c, Ob c r) => Functor (Beget c r) where
  type Dom (Beget c r) = Op c
  type Cod (Beget c r) = Nat c (->)
  fmap f = case observe f of
    Dict -> Nat $ _Beget id

instance (Category c, Ob c r, Ob c a) => Functor (Beget c r a) where
  type Dom (Beget c r a) = c
  type Cod (Beget c r a) = (->)
  fmap f = _Beget (f .)

beget :: (Category c, Ob c b) => (Beget c b b b -> Beget c b t t) -> c b t
beget l = runBeget $ l (Beget id)

(#) :: (Beget (->) b b b -> Beget (->) b t t) -> b -> t
(#) = beget

--------------------------------------------------------------------------------
-- * The Yoneda Lemma
--------------------------------------------------------------------------------

yoneda :: forall p f g a b. (Ob p a, FunctorOf p (->) g, FunctorOf p (->) (p b))
       => Iso (->) (->) (->)
          (Nat p (->) (p a) f)
          (Nat p (->) (p b) g)
          (f a)
          (g b)
yoneda = dimap hither yon where
  hither :: Nat p (->) (p a) f -> f a
  hither (Nat f) = f id
  yon :: g b -> Nat p (->) (p b) g
  yon gb = Nat $ \pba -> fmap pba gb

