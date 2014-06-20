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
import Prelude (Either(..), ($))

-- class Category (Hom :: i -> i -> *) => Weak (s :: (i -> i -> *) -> (i -> i -> *) -> (i -> i -> *)) | i -> s where
--  associateW :: s (s p q) r a c -> s p (s q r) a c
--  lambdaW :: s Hom p a b -> p a b
--  rhoW :: p a b -> s p Hom a b

class Hom ~ h => Category (h :: i -> i -> *) | i -> h where
  type Hom :: i -> i -> *
  id  :: forall (a :: i). Hom a a
  (.) :: forall (a :: i) (b :: i) (c :: i). Hom b c -> Hom a b -> Hom a c

instance Category (->) where
  type Hom = (->)
  id x = x
  (.) f g x = f (g x)

newtype (~>) (f :: i -> *) (g :: i -> *) = Nat { runNat :: forall a. f a -> g a }

instance Category ((~>) :: (i -> *) -> (i -> *) -> *) where
  type Hom = (~>)
  id = Nat id
  (.) (Nat f) (Nat g) = Nat (f . g)

newtype Lift (p :: * -> * -> *) (f :: i -> *) (g :: i -> *) (a :: i) = Lift { lower :: p (f a) (g a) }

instance PFunctor p => PFunctor (Lift p) where
  first (Nat f) = Nat (Lift . first f . lower)

class (Category (Hom :: x -> x -> *), Category (Hom :: y -> y -> *)) => Functor (f :: x -> y) where
  fmap :: Hom a b -> Hom (f a) (f b)

instance Prelude.Functor f => Functor f where
  fmap = Prelude.fmap

class (Category (Hom :: x -> x -> *), Category (Hom :: z -> z -> *)) => PFunctor (p :: x -> y -> z) where
  first :: Hom a b -> Hom (p a c) (p b c)

instance PFunctor (,) where first = Arrow.first
instance PFunctor Either where first = Arrow.left

class (Category (Hom :: y -> y -> *), Category (Hom :: z -> z -> *)) => QFunctor (p :: x -> y -> z) where
  second :: Hom a b -> Hom (p c a) (p c b)

instance QFunctor (,) where second = Arrow.second
instance QFunctor Either where second = Arrow.right

class (Category (Hom :: x -> x -> *), Category (Hom :: z -> z -> *)) => PContravariant (p :: x -> y -> z) where
  lmap :: Hom a b -> Hom (p b c) (p a c)

class (Category (Hom :: y -> y -> *), Category (Hom :: z -> z -> *)) => QContravariant (p :: x -> y -> z) where
  contramap :: Hom a b -> Hom (p c b) (p c a)

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
  rho       :: Hom a (p a (Id p)) -- inverse rho

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

data Prof :: (j -> k -> *) -> (i -> j -> *) -> i -> k -> * where
  Prof :: forall (p :: j -> k -> *) (q :: i -> j -> *) (a :: i) (b :: j) (c :: k). p b c -> q a b -> Prof p q a c

associateProf :: forall (p :: k -> l -> *) (q :: j -> k -> *) (r :: i -> j -> *) (a :: i) (c :: l). Prof (Prof p q) r a c -> Prof p (Prof q r) a c
associateProf (Prof (Prof a b) c) = Prof a (Prof b c)

lambdaProf :: forall (p :: i -> j -> *) (a :: i) (b :: j). QFunctor p => Prof Hom p a b -> p a b
lambdaProf (Prof h p) = rmap h p

rhoProf :: forall (p :: i -> k -> *) (a :: i) (b :: k). Category (Hom :: i -> i -> *) => p a b -> Prof p Hom a b
rhoProf p = Prof p id


{-
newtype Section a b    = Section { section :: Hom b a }
newtype Retraction a b = Retraction { retraction :: Hom b a }
newtype Op a b         = Op { op :: Hom b a }

instance Category c => Category (Iso c) where
  id = Iso id id
  Iso f f' . Iso g g' = Iso (f . g) (g' . f')

instance Category c => Category (Section c) where
  id = Section id
  Section f . Section g = Section (g . f)

instance Category c => Category (Retraction c) where
  id = Retraction id
  Retraction f . Retraction g = Retraction (g . f)

instance Category c => Category (Op c) where
  id = Op id
  Op f . Op g = Op (g . f)

class Isomorphic t => Sectioning t where
  sectioning :: k a b -> k b a -> t k b a

instance Sectioning Hom where
  sectioning _ = Hom

instance Sectioning Section where
  sectioning k _ = Section k

class Isomorphic t => Retracting t where
  retracting :: k a b -> k b a -> t k a b

instance Retracting Hom where
  retracting k _ = Hom k

instance Retracting Retraction where
  retracting _ = Retraction

class Isomorphic t where
  iso :: k a b -> k b a -> t k a b
  default iso :: Sectioning t => k a b -> k b a -> t k b a
  iso = sectioning

instance Isomorphic Hom where
  iso f _ = Hom f

instance Isomorphic Op where
  iso _ = Op

instance Isomorphic Section where
  iso _ = Section

instance Isomorphic Retraction where
  iso _ f = Retraction f

instance Isomorphic Iso where
  iso = Iso

class Profunctor p c d e | p -> c d e where
  dimap :: c a b -> d a' b' -> e (p b a') (p a b')

class Bifunctor (p :: x -> y -> z) (c :: x -> x -> *) (d :: y -> y -> *) (e :: z -> z -> *) | p -> c d e where
  bimap :: c a b -> d a' b' -> e (p a a') (p b b')

class Bifunctor p d d d => Tensor (p :: x -> x -> x) (d :: x -> x -> *) | p -> d where
  type Id p :: x
  associate :: Isomorphic t => t d (p (p a b) c) (p a (p b c))
  lambda :: Isomorphic t    => t d (p (Id p) a) a
  rho :: Isomorphic t       => t d (p a (Id p)) a

instance Bifunctor (,) (->) (->) (->) where
  bimap f g (a,b) = (f a, g b)

instance Tensor (,) (->) where
  type Id (,) = ()
  associate = iso (\((a,b),c) -> (a,(b,c))) (\(a,(b,c)) -> ((a,b),c))
  lambda    = iso (\((),a) -> a) ((,)())
  rho       = iso (\(a,()) -> a) (\a -> (a,()))

data Prof :: (y -> z -> *) -> (x -> y -> *) -> x -> z -> * where
  Prof :: p b c -> q a b -> Prof p q a c

-- build a skew weak category
-- we don't have enough universes to have non-endo-profunctors here with weak unitors!
class SkewCategory (s :: (i -> i -> *) -> (i -> i -> *) -> i -> i -> *) where
  type IdC s :: i -> i -> *
  associateC :: s (s p q) r a c -> s p (s q r) a c
  lambdaC    :: s (Id s) p a b -> p a b
  rhoC       :: p a b -> s p (Id s) a b

-- instance SkewCategory Prof where
--  type IdC Prof = (->)
-}
