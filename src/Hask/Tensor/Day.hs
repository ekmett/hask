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

--Day convolution on a monoidal category is associative making it a Semitensor
--To Do: define Isos

data Day3L (t :: i -> i -> i) (f :: i -> *) (g :: i -> *) (h :: i -> *) (a :: i) where
  Day3L :: (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, CopresheafOf c h, Ob c x, Ob c y, Ob c z)
         => c (t (t x y) z) a -> f x -> g y -> h z -> Day3L t f g h a

data Day3R (t :: i -> i -> i) (f :: i -> *) (g :: i -> *) (h :: i -> *) (a :: i) where
  Day3R :: (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, CopresheafOf c h, Ob c x, Ob c y, Ob c z)
         => c (t x (t y z)) a -> f x -> g y -> h z -> Day3R t f g h a

day3L :: Iso (Copresheaves c) (Copresheaves c) (->)
         (Day t (Day t f g) h) (Day t (Day t f' g') h')
         (Day3L t f g h)        (Day3L t f' g' h')
day3L = undefined
--this should use yoneda

day3R :: Iso (Copresheaves c) (Copresheaves c) (->)
         (Day t f (Day t g h)) (Day t f' (Day t g' h'))
         (Day3R t f g h)         (Day3R t f' g' h')
day3R = undefined
--mirror day3L

day3 :: Semitensor t
     => Iso (Copresheaves c) (Copresheaves c) (->)
        (Day3L t f g h) (Day3L t f' g' h')
        (Day3R t f g h) (Day3R t f' g' h')
day3 = undefined
--this should use associate

instance (Dom t ~ c, Category c, Semitensor t) => Semitensor (Day t) where
--  associate = (Un day3R) . day3 . day3L
  associate = undefined

--Here's the function giving me trouble. Gotta use something like it to build up day3.
--dayHither :: (Dom t ~ c, Category c, Semitensor t) => Day3L t f g h a -> Day3R t f g h a
--dayHither (Day3L c fx gy hz) = Day3R (c . beget associate) fx gy hz
