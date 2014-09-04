{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, AllowAmbiguousTypes, LambdaCase, DefaultSignatures, EmptyCase #-}
module Hask.Tensor.Day where

import Hask.Category
import Hask.Iso
import Hask.Tensor
import Prelude (undefined)

--------------------------------------------------------------------------------
-- * Day Convolution
--------------------------------------------------------------------------------

class FunctorOf c (->) f => CopresheafOf c f
instance FunctorOf c (->) f => CopresheafOf c f

data Day (t :: i -> i -> i) (f :: i -> *) (g :: i -> *) (a :: i) where
  Day :: (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, Ob c x, Ob c y)
      => c (t x y) a -> f x -> g y -> Day t f g a

--Day convolution of copresheaves is a copresheaf

instance (Dom t ~ c, CopresheafOf c f, CopresheafOf c g) => Functor (Day t f g) where
  type Dom (Day t f g) = Dom t
  type Cod (Day t f g) = (->)
  fmap c' (Day c fx gy) = Day (c' . c) fx gy

--Day convolution is a bifunctor of copresheaves

instance (Dom t ~ c, CopresheafOf c f) => Functor (Day t f) where
  type Dom (Day t f) = Copresheaves (Dom t)
  type Cod (Day t f) = Copresheaves (Dom t)
  fmap = fmap' where
    fmap' :: Copresheaves c g g' -> Copresheaves c (Day t f g) (Day t f g')
    fmap' (Nat natg) = Nat $ \(Day c fx gy) -> Day c fx (natg gy)

instance (Dom t ~ c, Category c) => Functor (Day t) where
  type Dom (Day t) = Copresheaves (Dom t)
  type Cod (Day t) = Nat (Copresheaves (Dom t)) (Copresheaves (Dom t))
  fmap = fmap' where
    fmap' :: Copresheaves c f f' -> Nat (Copresheaves c) (Copresheaves c) (Day t f) (Day t f')
    fmap' (Nat natf) = Nat $ Nat $ \(Day c fx gy) -> Day c (natf fx) gy

--Day convolution on a monoidal category is associative

instance (Semitensor t, Dom t ~ c, Category c) => Semitensor (Day t) where
  associate = dimap (Nat hither) (Nat yon) where
    hither :: Day t (Day t f g) h a -> Day t f (Day t g h) a
    hither (Day (c' :: c (t b z) a) (Day (c :: c (t x y) b) fx gy) hz) =
      case semitensorClosed :: Dict (Ob c (t y z)) of
        Dict -> case semitensorClosed :: Dict (Ob c (t x (t y z))) of
          Dict -> Day (c' . runNat (fmap c) . beget associate) fx (Day id gy hz)
    yon :: Day t f (Day t g h) a -> Day t (Day t f g) h a
    yon (Day (c' :: c (t x b) a) fx (Day (c :: c (t y z) b) gy hz)) =
      case semitensorClosed :: Dict (Ob c (t x y)) of
        Dict -> case semitensorClosed :: Dict (Ob c (t y z)) of
          Dict -> case semitensorClosed :: Dict (Ob c (t x (t y z))) of
            Dict -> Day (c' . fmap1 c . get associate) (Day id fx gy) hz

--Day convolution on a monoidal category is left & right unital

--type instance (Dom t ~ c, Category c) => I (Day t) = c (I t)