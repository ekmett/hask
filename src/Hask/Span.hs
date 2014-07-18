{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Hask.Span where

import Hask.Core
import Data.Reflection

-- the wedge scheme used for pullbacks and pushouts
data Λ = X | Y | Z

data instance Scheme (a :: Λ) (b :: Λ) where
  I :: forall (a :: Λ). Scheme a a
  L :: Scheme 'X 'Y
  R :: Scheme 'X 'Z

type instance Hom = (Scheme :: Λ -> Λ -> *)

instance Category (Scheme :: Λ -> Λ -> *) where
  id = I
  x . I = x
  I . x = x
  _ . _ = undefined

type Pushout f g x y z   = Colim (Span f g x y z)
type Pullback f g x y z  = Lim (Cospan f g x y z)
type Coequalizer f g x z = Pushout f g x z z
type Equalizer f g x z   = Pullback f g x z z

-- Const a provides the trivial span when the index is set to come from (Λ)

type family XYZ (x :: i) (y :: i) (z :: i) (w :: Λ) :: i where
  XYZ x y z 'X = x
  XYZ x y z 'Y = y
  XYZ x y z 'Z = z

type family Span :: l -> r -> i -> i -> i -> Λ -> i
newtype Span0 l r x y z w = Span { runSpan :: XYZ x y z w }
type instance Span = Span0
_Span = dimap runSpan Span

instance (Reifies l (x -> y), Reifies r (x -> z)) => Functor (Span0 l r x y z) where
  fmap I w = w
  fmap L (Span x) = Span (reflect (Proxy :: Proxy l) x)
  fmap R (Span x) = Span (reflect (Proxy :: Proxy r) x)

data ReifiedId a = ReifiedId
instance Reifies (ReifiedId a) (a -> a) where reflect _ = id
instance Category (Cod f) => Reifies (ReifiedId f) (Nat f f) where reflect _ = id
instance Reifies (ReifiedId a) (a :- a) where reflect _ = id

-- trivial span for an object
type Ob x = Span ReifiedId ReifiedId x x x

-- trivial span for a morphism 
type Mor r x = Span ReifiedId r x x

type family Cospan :: l -> r -> i -> i -> i -> Λ -> i
newtype Cospan0 f g x y z w = Cospan { runCospan :: XYZ x y z w }
type instance Cospan = Cospan0
_Cospan = dimap runCospan Cospan

instance (Reifies l (y -> x), Reifies r (z -> x)) => Contravariant (Cospan0 l r x y z) where
  contramap I w = w
  contramap L (Cospan y) = Cospan (reflect (Proxy :: Proxy l) y)
  contramap R (Cospan z) = Cospan (reflect (Proxy :: Proxy r) z)

