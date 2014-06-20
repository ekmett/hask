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
import qualified Data.Functor.Contravariant as Contra
import Control.Category (Category(..))
import qualified Control.Arrow as Arrow
import qualified Prelude
import Prelude (Either(..), ($), either)

type family Hom :: i -> i -> *
type instance Hom = (->)
type instance Hom = (~>)

newtype f ~> g = Nat { runNat :: forall a. f a -> g a }

instance Category (~>) where
  id = Nat id
  Nat f . Nat g = Nat (f . g)

class Functor (f :: x -> y) where
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

class Contravariant (f :: x -> y) where
  contramap :: Hom b a -> Hom (f a) (f b)

instance Contra.Contravariant f => Contravariant f where
  contramap = Contra.contramap

class PFunctor (p :: x -> y -> z) where
  first :: Hom a b -> Hom (p a c) (p b c)

instance PFunctor (,) where first = Arrow.first
instance PFunctor Either where first = Arrow.left
instance PFunctor p => PFunctor (Lift p) where
  first (Nat f) = Nat (_Lift $ first f)

class QFunctor (p :: x -> y -> z) where
  second :: Hom a b -> Hom (p c a) (p c b)

instance QFunctor (->) where second = (.)
instance QFunctor (~>) where second = (.)
instance QFunctor (,) where second = Arrow.second
instance QFunctor Either where second = Arrow.right
instance QFunctor (Const :: * -> i -> *) where second _ = _Const id
instance QFunctor p => QFunctor (Lift p) where
  second (Nat f) = Nat (_Lift $ second f)
instance QFunctor At where
  second (Nat f) = _At f

class PContravariant (p :: x -> y -> z) where
  lmap :: Hom a b -> Hom (p b c) (p a c)

instance PContravariant (->) where lmap f g = g . f
instance PContravariant (~>) where lmap f g = g . f
instance PContravariant p => PContravariant (Lift p) where lmap (Nat f) = Nat $ _Lift (lmap f)

class QContravariant (p :: x -> y -> z) where
  qmap :: Hom a b -> Hom (p c b) (p c a)

instance QContravariant (Const :: * -> i -> *) where qmap _ = _Const id
instance QContravariant p => QContravariant (Lift p) where qmap (Nat f) = Nat $ _Lift (qmap f)
instance Contravariant (Const k :: i -> *) where contramap _ = _Const id

class (PFunctor p, QFunctor p) => Bifunctor (p :: x -> y -> z)
instance (PFunctor p, QFunctor p) => Bifunctor (p :: x -> y -> z)

class (PContravariant p, QFunctor p) => Profunctor (p :: x -> y -> z)
instance (PContravariant p, QFunctor p) => Profunctor (p :: x -> y -> z)

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

class (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)
instance (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)

class (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)
instance (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)

rmap :: QFunctor p => Hom a b -> Hom (p c a) (p c b)
rmap = second

bimap :: (Category (Hom :: z -> z -> *), Bifunctor (p :: x -> y -> z)) => Hom a b -> Hom c d -> Hom (p a c) (p b d)
bimap f g = first f . second g

dimap :: (Category (Hom :: z -> z -> *), Profunctor (p :: x -> y -> z)) => Hom a b -> Hom c d -> Hom (p b c) (p a d)
dimap f g = lmap f . rmap g

-- tensor for a skew monoidal category
class (Bifunctor p, Category (Hom :: x -> x -> *)) => Tensor (p :: x -> x -> x) where
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

class Terminal t where
  terminal :: Hom a t

instance Terminal () where
  terminal _ = ()

instance Terminal (Const ()) where
  terminal = Nat $ \_ -> Const ()

class Initial t where
  initial :: Hom t a

instance Initial Void where
  initial = absurd

instance Initial (Const Void) where
  initial = Nat $ absurd . getConst

class (h ~ Hom, Symmetric ((*)::i->i->i), Tensor ((*)::i->i->i), Terminal (Id ((*)::i->i->i))) => Cartesian (h :: i -> i -> *) | i -> h where
  type (*) :: i -> i -> i
  fst   :: forall (a :: i) (b :: i). Hom (a * b) a
  snd   :: forall (a :: i) (b :: i). Hom (a * b) b
  (&&&) :: forall (a :: i) (b :: i) (c :: i). Hom a b -> Hom a c -> Hom a (b * c)

instance Cartesian (->) where
  type (*) = (,)
  fst   = Prelude.fst
  snd   = Prelude.snd
  (&&&) = (Arrow.&&&)

instance Cartesian (~>) where
  type (*) = Lift (,)
  fst = Nat $ fst . lower
  snd = Nat $ snd . lower
  Nat f &&& Nat g = Nat $ Lift . (f &&& g)

class (Cartesian (Hom :: i -> i -> *), Profunctor p) => Strong (p :: i -> i -> *) where
  {-# MINIMAL _1 | _2 #-}
  _1 :: p a b -> p (a * c) (b * c)
  _1 = dimap swap swap . _2
  _2 :: p a b -> p (c * a) (c * b)
  _2 = dimap swap swap . _1

instance Strong (->) where
  _1 = first
  _2 = second

instance Strong (~>) where
  _1 = first
  _2 = second

type Lens s t a b = forall p. Strong p => p a b -> p s t

class (h ~ Hom, Symmetric ((+)::i->i->i), Tensor ((+)::i->i->i),Initial (Id ((+)::i->i->i))) => Cocartesian (h :: i -> i -> *) | i -> h where
  type (+) :: i -> i -> i
  inl    :: forall (a :: i) (b :: i). Hom a (a + b)
  inr    :: forall (a :: i) (b :: i). Hom b (a + b)
  (|||)  :: forall (a :: i) (b :: i) (c :: i). Hom a c -> Hom b c -> Hom (a + b) c

instance Cocartesian (->) where
  type (+) = Either
  inl = Left
  inr = Right
  (|||) = either

instance Cocartesian (~>) where
  type (+) = Lift Either
  inl = Nat (Lift . Left)
  inr = Nat (Lift . Right)
  Nat f ||| Nat g = Nat $ either f g . lower

class (Cocartesian (Hom :: i -> i -> *), Profunctor p) => Choice (p :: i -> i -> *) where
  {-# MINIMAL _Left | _Right #-}
  _Left  :: p a b -> p (a + c) (b + c)
  _Left = dimap swap swap . _Right
  _Right :: p a b -> p (c + a) (c + b)
  _Right = dimap swap swap . _Left

instance Choice (->) where
  _Left = Arrow.left
  _Right = Arrow.right

instance Choice (~>) where
  _Left (Nat f) = Nat $ _Lift (_Left f)
  _Right (Nat g) = Nat $ _Lift (_Right g)

type Prism s t a b = forall p. Choice p => p a b -> p s t
