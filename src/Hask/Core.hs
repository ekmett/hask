{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2008-2014 and Sjoerd Visscher 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- This package explores category theory via a couple of non-standard
-- tricks.
--
-- First, we use lens-style isomorphism-families to talk about
-- most operations.
--
-- Second, we heavily abuse parametricity as a proxy for naturality.
-- This means that the category Nat that gets used throughout is a
-- particularly well-behaved. An inhabitant of @Nat :: (i -> j) -> (i -> j) -> *@
-- is required to be polymorphic in its argument.
--
-- Parametricity is a very strong notion of naturality. Notably, we
-- don't have to care if i or j are co -or- contravariant. (forall a. f a ~> g a)
-- respects _both_ -- at least so long as the 'functors' involved aren't GADTs.
--
-- Third, we use kind-indexing to pick the category. This means it
-- is harder to talk about Kleisli categories, etc. but in exchange
-- most of the category selection _just works_. A central working
-- hypothesis of this code is that this is sufficient to talk about
-- interesting categories, and it certainly results in less verbose
-- code than more explicit encodings which clutter up every type class
-- talking about the choice of category.
--
-- Here, much of the time the selection is implicit.
--------------------------------------------------------------------
module Hask.Core
  ( Hom, type (~>), type (^)
  , Dom, Cod, Cod2, Arr, Enriched, Internal, External, Natural

  -- * Natural transformations
  , Nat(Nat, runNat), nat2, nat3, runNat2, runNat3, runNat4

  -- * Functors
  , Functor(fmap), first
  , Contravariant(contramap), lmap

  -- * Functor composition
  , Composed(..), type (·), composed, associateCompose
  , whiskerComposeL
  , whiskerComposeR
  , lambdaCompose
  , rhoCompose

  -- ** In the limit
  , Post

  -- ** Derived notions
  , fmap1, contramap1
  , Bifunctor, bimap
  , Profunctor, dimap
  , Phantom

  -- * Colim -| Const -| Lim
  , Cocomplete(..)
  , Constant(..)
  , Complete(..)

  -- * Natural Isomorphisms
  , Iso
  -- * Adjunctions
  , (-|)(..)
  , unitAdj, counitAdj, zipR, absurdL, cozipL
  -- ** Currying
  , Curried(..), curried, ccc
  -- ** Cocurrying
  , Cocurried(..), cocurried
  -- * Automatic Lifting
  , Lifted(..)
  -- * Constraints
  , (:-)(Sub), Dict(Dict), (\\), type (&), (|-)(implies), _Sub, _Implies
  -- * Lens Esoterica

  -- ** The Yoneda embedding
  , Get(..), _Get, get
  , Beget(..), _Beget, beget, (#)

  -- ** Inverting natural isomorphisms
  , Un(..), _Un, un
  , Via(..), via, mapping, lmapping, swapping, firstly, post, pre

  -- ** Hom as a Profunctor
  , Self(..), _Self

  -- * Monoidal Categories
  , Semitensor(..)
  , I
  , Tensor(..)
  , Symmetric(..)

  -- * Closed Categories
  , Closed(..)

  -- * Terminal and Initial Objects
  , Terminal(..)
  , Initial(..)

  -- * Copowers and Cartesian Categories
  , Copower, type (*)
  , Precartesian(..)
  , Cartesian

  , Precocartesian(..)
  , Cocartesian

  -- * Distributive bicartesian categories
  , Distributive(..)

  -- * CCC's
  , CCC

  -- * Monoidal Functors
  , Semimonoidal(..), ap, ap2Applicative
  , Monoidal(..), return
  , Cosemimonoidal(..)
  , Comonoidal(..)

  -- * Monads
  , Semimonad(..)
  , Monad
  , Cosemimonad(..)
  , Comonad(..)

  -- * Monoids
  , Semigroup(..), multM
  , Monoid(..), oneM, mappend
  , Cosemigroup(..), zeroOp
  , Comonoid(..), comultOp

  -- * Strength
  , Strength(..)
  , Costrength(..)

  -- * Identity functors
  , Identity(..)

  -- * Kan extensions
  , HasRan(..)
  , HasLan(..)

  -- * Categories
  -- ** Products
  , Prod(..), runProd, runFst, runSnd, diagProdAdj, sumDiagAdj
  -- ** Unit
  , Unit(..)
  -- ** Empty
  , Empty(..), No

  -- * Candidates for Removal:
  , Semicategory

  -- * Internals
  -- ** Categories
  -- ** Composition
  , Compose1(..), Compose2(..), ComposeC
  -- ** Limits
  , Lim1(..), Lim2(..), Lim3(..), LimC(..)
  , Const1(..), Const2(..), ConstC
  , Colim1(..), Colim2(..)
  -- ** Identities
  , Id1(..), IdC
  -- ** Lifts
  , Lift1(..), Lift2(..), LiftC
  -- ** Copowers
  , Copower1(..), Copower2(..), Copower2_1(..)
  -- ** Kan extensions
  , Ran1(..), Lan1(..), Lan2(..)
  -- ** Base Re-exports
  , Constraint
  -- ** Prelude Re-Exports
  , undefined, ($)
  , Either(..), Maybe(..)
  -- ** Re-exports
  , Tagged(..), Proxy(..), Category(..), Void, absurd
  ) where


import qualified Control.Applicative as Base
import qualified Control.Arrow as Arrow
import Control.Category (Category(..))
import qualified Data.Constraint as Constraint
import Data.Constraint ((:-)(Sub), (\\), Dict(Dict))
import qualified Data.Functor as Base
import qualified Data.Functor.Identity as Base
import Data.Proxy
import Data.Tagged
import qualified Data.Traversable as Base
import Data.Void
import qualified Prelude
import Prelude (Either(..), ($), either, Bool, undefined, Maybe(..))
import GHC.Exts (Constraint, Any)
import Unsafe.Coerce (unsafeCoerce)

-- * A kind-indexed family of categories

infixr 0 ~>, `Nat`, `Hom`

-- | All of our categories will be denoted by the kinds of their arguments.
--
-- This is allows for enriched Homs
type family Hom :: i -> i -> k
type instance Hom = (->)     -- @* -> * -> *@
type instance Hom = Nat      -- @(i -> j) -> (i -> j) -> *@
type instance Hom = (:-)     -- @Constraint -> Constraint -> *@
type instance Hom = Unit     -- @() -> () -> *@
type instance Hom = Empty    -- @Void -> Void -> *@
type instance Hom = Prod     -- @(i,j) -> (i, j) -> *@
type instance Hom = Lift Hom -- automatically support Nat-enrichment, etc.
type instance Hom = (|-)     -- @Constraint -> Constraint -> Constraint@ the internal hom of (:-)

-- a boring unenriched Hom
type (~>) = (Hom :: i -> i -> *)

-- * convenience types that make it so we can avoid explicitly talking about the kinds as much as possible
type Dom  (f :: i -> j)      = (Hom :: i -> i -> *)
type Cod  (f :: i -> j)      = (Hom :: j -> j -> *)
type Cod2 (f :: i -> j -> k) = (Hom :: k -> k -> *)
type Arr  (a :: i)           = (Hom :: i -> i -> *)

type Enriched (k :: i -> i -> *) = (Hom :: i -> i -> j)
type Internal (k :: i -> i -> *) = (Hom :: i -> i -> i)
type External (k :: i -> i -> j) = (Hom :: i -> i -> *)
type Natural  (k :: j -> j -> *) = (Hom :: (i -> j) -> (i -> j) -> *)

infixr 8 ^
type a ^ b = Internal Hom b a

-- * Natural transformations (by using parametricity these are very strong)

newtype Nat f g = Nat { runNat :: forall a. f a ~> g a }

nat2 :: (forall a b. f a b ~> g a b) -> f ~> g
nat2 f = Nat (Nat f)

nat3 :: (forall a b c. f a b c ~> g a b c) -> f ~> g
nat3 f = Nat (Nat (Nat f))

runNat2 = runNat . runNat
runNat3 = runNat . runNat . runNat
runNat4 = runNat . runNat . runNat . runNat

instance Category ((~>) :: j -> j -> *) => Category (Nat :: (i -> j) -> (i -> j) -> *) where
  id = Nat id
  Nat f . Nat g = Nat (f . g)

-- * Functors between these kind-indexed categories

class Functor (f :: x -> y) where
  fmap :: (a ~> b) -> f a ~> f b

instance Functor [] where fmap = Base.fmap
instance Functor Maybe where fmap = Base.fmap

first :: Functor f => (a ~> b) -> f a c ~> f b c
first = runNat . fmap

class Contravariant f where
  contramap :: (b ~> a) -> f a ~> f b

lmap :: Contravariant f => (a ~> b) -> f b c ~> f a c
lmap = runNat . contramap

-- * Bifunctors/profunctors through limits

-- | @LimC :: (i -> Constraint) -> Constraint@ takes limits in the category of constraints
--
-- @type instance Lim = LimC@
class LimC (p :: i -> Constraint) where
  limDict :: Dict (p a)

-- Abuses @Any@ because it inhabits every kind, not a good choice of Skolem, but the best we have

-- If you make any instances for @Any@, this will burn your house down and scatter the ashes. Don't do that.
instance p Any => LimC (p :: i -> Constraint) where
  limDict = case unsafeCoerce (id :: p Any :- p Any) :: p Any :- p a of
    Sub d -> d

instance Functor LimC where
  fmap f = dimap (Sub limDict) (Sub Dict) (runAny f) where
    runAny :: (p ~> q) -> p Any ~> q Any
    runAny = runNat

class (hom ~ Hom) => Composed (hom :: k -> k -> *) | k -> hom where
  type Compose :: (j -> k) -> (i -> j) -> i -> k
  compose   :: f (g a) `hom` Compose f g a
  decompose :: Compose f g a `hom` f (g a)

infixr 9 ·
type (·) = Compose

-- | We can compose constraints
class f (g a) => ComposeC f g a
instance f (g a) => ComposeC f g a

instance Composed (:-) where
  type Compose = ComposeC
  compose   = Sub Dict
  decompose = Sub Dict

class LimC (f · p) => Post f p
instance LimC (f · p) => Post f p

fmap1 :: forall p a b c. Post Functor p => (a ~> b) -> p c a ~> p c b
fmap1 f = case limDict :: Dict (Compose Functor p c) of Dict -> fmap f

contramap1 :: forall p a b c. Post Contravariant p => (a ~> b) -> p c b ~> p c a
contramap1 f = case limDict :: Dict (Compose Contravariant p c) of Dict -> contramap f

class (Functor p, Post Functor p) => Bifunctor p
instance (Functor p, Post Functor p) => Bifunctor p

bimap :: (Bifunctor p, Category (Cod2 p)) => (a ~> b) -> (c ~> d) -> p a c ~> p b d
bimap f g = first f . fmap1 g

class (Contravariant p, Post Functor p) => Profunctor p
instance (Contravariant p, Post Functor p) => Profunctor p

dimap :: (Profunctor p, Category (Cod2 p)) => (a ~> b) -> (c ~> d) -> p b c ~> p a d
dimap f g = lmap f . fmap1 g

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

-- * Adjunctions

infixr 0 -|

-- | @f -| u@ indicates f is left adjoint to u
class (Functor f, Functor u) => f -| u | f -> u, u -> f where
  adj :: Iso (f a ~> b) (f a' ~> b') (a ~> u b) (a' ~> u b')

unitAdj :: (f -| u, Category (Dom u)) => a ~> u (f a)
unitAdj = get adj id

counitAdj :: (f -| u, Category (Dom f)) => f (u b) ~> b
counitAdj = beget adj id

-- given f -| u, u is a strong monoidal functor
--
-- @
-- ap0 = get adj terminal
-- ap2 = get zipR
-- @
zipR :: (f -| u, Cartesian (Dom u), Cartesian (Cod u))
     => Iso (u a * u b) (u a' * u b') (u (a * b)) (u (a' * b'))
zipR = dimap (get adj (beget adj fst &&& beget adj snd))
             (fmap fst &&& fmap snd)

absurdL :: (f -| u, Initial z) => Iso z z (f z) (f z)
absurdL = dimap initial (beget adj initial)

cozipL :: (f -| u, Cocartesian (Cod u), Cocartesian (Cod f))
       => Iso (f (a + b)) (f (a' + b')) (f a + f b) (f a' + f b')
cozipL = dimap
  (beget adj (get adj inl ||| get adj inr))
  (fmap inl ||| fmap inr)

-- tabulated :: (f -| u) => Iso (a ^ f One) (b ^ f One) (u a) (u b)
-- splitL :: (f -| u) => Iso (f a) (f a') (a * f One) (a' * f One)

-- these are all the instances of kind * -> *
--
-- Unfortunately that isn't true, as functors to/from k -> * that are polymorphic in k
-- overlap with these instances!
--
-- instance Base.Functor f => Functor f where
--   fmap = Prelude.fmap

-- instance Contravariant.Contravariant f => Contravariant f where
--    contramap = Contravariant.contramap

instance Category ((~>) :: j -> j -> *) => Functor (Nat f :: (i -> j) -> *) where
  fmap = (.)

instance Functor ((:-) f) where
  fmap = fmap1

-- .. and back
class Const ~ k => Constant (k :: j -> i -> j) | j i -> k where
  type Const :: j -> i -> j
  _Const :: Iso (k b a) (k b' a') b b'

newtype Const1 b a = Const { getConst :: b }

instance Constant Const1 where
  type Const = Const1
  _Const = dimap getConst Const

instance Functor Const1 where
  fmap f = Nat (_Const f)

instance Functor (Const1 b) where
  fmap _ = _Const id

instance Contravariant (Const1 b) where
  contramap _ = _Const id

instance (Semigroup b, Precartesian ((~>) :: i -> i -> *)) => Semimonoidal (Const1 b :: i -> *) where
  ap2 = beget _Const . mult . bimap (get _Const) (get _Const)

instance (Monoid b, Cartesian ((~>) :: i -> i -> *)) => Monoidal (Const1 b :: i -> *) where
  ap0 = beget _Const . one

instance Semigroup b => Semigroup (Const1 b a) where
  mult = beget _Const . mult . bimap (get _Const) (get _Const)

instance Monoid b => Monoid (Const1 b a) where
  one = beget _Const . one

instance (Cosemigroup b, Precocartesian ((~>) :: i -> i -> *)) => Cosemimonoidal (Const1 b :: i -> *) where
  op2 = bimap (beget _Const) (beget _Const) . comult . get _Const

instance (Comonoid b, Cocartesian ((~>) :: i -> i -> *)) => Comonoidal (Const1 b :: i -> *) where
  op0 = zero . get _Const

instance Cosemigroup b => Cosemigroup (Const1 b a) where
  comult = bimap (beget _Const) (beget _Const) . comult . get _Const

instance Comonoid b => Comonoid (Const1 b a) where
  zero = zero . get _Const

newtype Const2 (f :: j -> *) (a :: i) (c :: j) = Const2 { getConst2 :: f c }

instance Constant Const2 where
  type Const = Const2
  _Const = dimap (Nat getConst2) (Nat Const2)

instance Functor Const2 where
  fmap f = Nat (_Const f)

instance Functor (Const2 f) where
  fmap _ = Nat $ Const2 . getConst2

instance Functor f => Functor (Const2 f a) where
  fmap f = Const2 . fmap f . getConst2

instance (Semigroup b, Precartesian ((~>) :: i -> i -> *)) => Semimonoidal (Const2 b :: i -> j -> *) where
  ap2 = beget _Const . mult . bimap (get _Const) (get _Const)

instance (Monoid b, Cartesian ((~>) :: i -> i -> *)) => Monoidal (Const2 b :: i -> j -> *) where
  ap0 = beget _Const . one

instance Semigroup b => Semigroup (Const2 b a) where
  mult = beget _Const . mult . bimap (get _Const) (get _Const)

instance Monoid b => Monoid (Const2 b a) where
  one = beget _Const . one

instance (Cosemigroup b, Precocartesian ((~>) :: i -> i -> *)) => Cosemimonoidal (Const2 b :: i -> j -> *) where
  op2 = bimap (beget _Const) (beget _Const) . comult . get _Const

instance (Comonoid b, Cocartesian ((~>) :: i -> i -> *)) => Comonoidal (Const2 b :: i -> j -> *) where
  op0 = zero . get _Const

instance Cosemigroup b => Cosemigroup (Const2 b a) where
  comult = bimap (beget _Const) (beget _Const) . comult . get _Const

instance Comonoid b => Comonoid (Const2 b a) where
  zero = zero . get _Const

class b => ConstC b a
instance b => ConstC b a

instance Constant ConstC where
  type Const = ConstC
  _Const = dimap (Sub Dict) (Sub Dict)

instance Functor ConstC where
  fmap f = Nat (_Const f)

instance Functor (ConstC b) where
  fmap _ = Sub Dict

instance (Semigroup b, Precartesian ((~>) :: i -> i -> *)) => Semimonoidal (ConstC b :: i -> Constraint) where
  ap2 = beget _Const . mult . bimap (get _Const) (get _Const)

instance (Monoid b, Cartesian ((~>) :: i -> i -> *)) => Monoidal (ConstC b :: i -> Constraint) where
  ap0 = beget _Const . one

-- instance Semigroup b => Semigroup (ConstC b a) -- all constraints form a semigroup already

instance Monoid b => Monoid (ConstC b a) where
  one = beget _Const . one

instance (Cosemigroup b, Precocartesian ((~>) :: i -> i -> *)) => Cosemimonoidal (ConstC b :: i -> Constraint) where
  op2 = bimap (beget _Const) (beget _Const) . comult . get _Const

instance (Comonoid b, Cocartesian ((~>) :: i -> i -> *)) => Comonoidal (ConstC b :: i -> Constraint) where
  op0 = zero . get _Const

instance Cosemigroup b => Cosemigroup (ConstC b a) where
  comult = bimap (beget _Const) (beget _Const) . comult . get _Const

instance Comonoid b => Comonoid (ConstC b a) where
  zero = zero . get _Const

newtype Lim1 (f :: i -> *) = Lim { getLim :: forall x. f x }
-- type instance Lim = Lim1

instance Functor Lim1 where
  fmap (Nat f) (Lim g) = Lim (f g)

instance Semimonoidal Lim1 where
  ap2 (Lim f, Lim g) = Lim (Lift (f, g))

instance Monoidal Lim1 where
  ap0 () = Lim $ Const ()

instance Semigroup m => Semigroup (Lim1 m) where
  mult = multM

instance Monoid m => Monoid (Lim1 m) where
  one = oneM

instance Const1 -| Lim1 where
  adj = dimap (\f a -> Lim (runNat f (Const a))) $ \h -> Nat $ getLim . h . getConst

newtype Lim2 (f :: i -> j -> *) (y :: j) = Lim2 { getLim2 :: forall x. f x y }
-- type instance Lim = Lim2

newtype Lim3 (f :: i -> j -> k -> *) (y :: j) (z :: k) = Lim3 { getLim3 :: forall x. f x y z }
-- type instance Lim = Lim3

instance Functor Lim2 where
  fmap f = Nat $ \(Lim2 g) -> Lim2 (runNat (runNat f) g)

-- instance Monoidal Lim2 -- instantiate when Nat on 2 arguments is made Cartesian

instance Const2 -| Lim2 where
  adj = dimap (\(Nat f) -> Nat $ \ a -> Lim2 (runNat f (Const2 a))) $ \(Nat h) -> nat2 $ getLim2 . h . getConst2

instance Semimonoidal LimC where
  ap2 = get zipR

instance Monoidal LimC where
  ap0 = Sub Dict

-- instance Semigroup m => Semigroup (LimC m) where mult = multM

instance Monoid m => Monoid (LimC m) where
  one = oneM

instance ConstC -| LimC where
  adj = dimap (hither . runNat) (\b -> Nat $ dimap (Sub Dict) (Sub limDict) b) where
    hither :: (ConstC a Any :- f Any) -> a :- LimC f
    hither = dimap (Sub Dict) (Sub Dict)

-- | A complete category has all small limits.

class hom ~ Hom => Complete (hom :: j -> j -> *) | j -> hom where
  type Lim :: (i -> j) -> j

  elim :: hom (Lim g) (g a)

  -- The explicit witness here allows us to quantify over all kinds i.
  complete :: Dict (Const -| (Lim :: (i -> j) -> j))
  default complete :: (Const -| (Lim :: (i -> j) -> j)) => Dict (Const -| (Lim :: (i-> j) -> j))
  complete = Dict

instance Complete (->) where
  type Lim = Lim1
  elim = getLim
  complete = Dict

instance Complete (Nat :: (i -> *) -> (i -> *) -> *) where
  type Lim = Lim2
  elim = Nat getLim2
  complete = Dict

instance Complete ((:-) :: Constraint -> Constraint -> *) where
  type Lim = LimC
  elim = Sub limDict
  complete = Dict

--instance Limited Lim3 where
--  elim = nat2 getLim3

{-
-- all functors to * are continuous
continuous :: (Functor f, Complete (Dom f)) => f (l g) -> Lim (f · g)
continuous f = Lim $ compose (fmap elim f)

-- all functors to k -> * are continuous
continuous1 :: (Functor f, Complete (Dom f)) => f (l g) `Nat` Lim (Compose2 f g)
continuous1 = Nat $ \f -> Lim2 $ runNat (compose . fmap elim) f

-- all functors to Constraint are continuous
continuousC :: (Functor f, Complete (Dom f)) => f (l g) :- Lim (ComposeC f g)
continuousC = limC . fmap elim where
  limC :: f (g Any) :- LimC (ComposeC f g)
  limC = Sub Dict

-}
-- * Support for Tagged and Proxy

instance Functor Tagged where
  fmap _ = Nat (_Tagged id)

instance Functor (Tagged e) where
  fmap = Prelude.fmap

_Tagged :: Iso (Tagged s a) (Tagged t b) a b
_Tagged = dimap unTagged Tagged

instance Functor Proxy where
  fmap _ Proxy = Proxy

instance Contravariant Proxy where
  contramap _ Proxy = Proxy

-- * Dictionaries

-- Dict :: Constraint -> * switches categories from the category of constraints to Hask
instance Functor Dict where
  fmap p Dict = Dict \\ p

-- * Lift

-- Lifting lets us define things an index up from simpler parts, recycle products, etc.

class Lift ~ s => Lifted (s :: (j -> k -> l) -> (i -> j) -> (i -> k) -> i -> l) | i j k l -> s where
  type Lift :: (j -> k -> l) -> (i -> j) -> (i -> k) -> i -> l
  _Lift :: Iso (s q f g a) (s r h e b) (q (f a) (g a)) (r (h b) (e b))

-- ** Lift1

newtype Lift1 p f g a = Lift { lower :: p (f a) (g a) }

instance Lifted Lift1 where
  type Lift = Lift1
  _Lift = dimap lower Lift

instance Functor Lift1 where
  fmap f = nat3 $ _Lift $ runNat2 f

instance Functor p => Functor (Lift1 p) where
  fmap f = nat2 $ _Lift $ first $ runNat f

instance Contravariant p => Contravariant (Lift1 p) where
  contramap f = nat2 $ _Lift $ lmap $ runNat f

instance Post Contravariant p => Contravariant (Lift1 p f) where
  contramap (Nat f) = Nat $ _Lift (contramap1 f)

instance Post Functor p => Functor (Lift1 p f) where
  fmap (Nat f) = Nat (_Lift $ fmap1 f)

instance (Functor p, Post Functor p, Functor f, Functor g) => Functor (Lift1 p f g) where
  fmap f = _Lift (bimap (fmap f) (fmap f))

-- ** LiftC

class r (p a) (q a) => LiftC r p q a
instance r (p a) (q a) => LiftC r p q a

instance Functor p => Functor (LiftC p) where
  fmap f = nat2 $ _Lift $ first $ runNat f

instance Contravariant p => Contravariant (LiftC p) where
  contramap f = nat2 $ _Lift $ lmap $ runNat f

instance Post Functor p => Functor (LiftC p e) where
  fmap (Nat f) = Nat (_Lift $ fmap1 f)

instance Post Contravariant p => Contravariant (LiftC p e) where
  contramap (Nat f) = Nat (_Lift $ contramap1 f)

instance Lifted LiftC where
  type Lift = LiftC
  _Lift = dimap (Sub Dict) (Sub Dict)

-- ** Lift2

newtype Lift2 p f g a b = Lift2 { lower2 :: p (f a) (g a) b }

instance Lifted Lift2 where
  type Lift = Lift2
  _Lift = dimap (Nat lower2) (Nat Lift2)

instance Functor Lift2 where
  fmap f = nat3 $ _Lift $ runNat2 f

instance Functor p => Functor (Lift2 p) where
  fmap f = nat2 $ _Lift $ first $ runNat f

instance Contravariant p => Contravariant (Lift2 p) where
  contramap f = nat2 $ _Lift $ lmap $ runNat f

instance Post Functor p => Functor (Lift2 p f) where
  fmap (Nat f) = Nat (_Lift $ fmap1 f)

instance Post Contravariant p => Contravariant (Lift2 p f) where
  contramap = contramap1

-- Lifting adjunctions

curry1 :: forall a b c p q x. (Curried p q, Post (Curryable p) a) => (p (a x) (b x) ~> c x) -> a x ~> q (b x) (c x)
curry1 = case limDict :: Dict (Compose (Curryable p) a x) of Dict -> curry

instance Curried p q => Curried (Lift1 p) (Lift1 q) where
  type Curryable (Lift1 p) = Post (Curryable p)
  curry f = Nat $ beget _Lift . curry1 (runNat f . beget _Lift)
  uncurry g = Nat $ uncurry (get _Lift . runNat g) . get _Lift

instance Curried p q => Curried (Lift2 p) (Lift2 q) where
  type Curryable (Lift2 p) = Post (Curryable p)
  curry f = Nat $ beget _Lift . curry1 (runNat f . beget _Lift)
  uncurry g = Nat $ uncurry (get _Lift . runNat g) . get _Lift

instance Curried p q => Curried (LiftC p) (LiftC q) where
  type Curryable (LiftC p) = Post (Curryable p)
  curry f = Nat $ beget _Lift . curry1 (runNat f . beget _Lift)
  uncurry g = Nat $ uncurry (get _Lift . runNat g) . get _Lift

-- instance (f -| g, f' -| g') => Lift1 Either f f' -| Lift1 (,) g g' where ?
-- instance (Post Functor p, Post Functor q, Compose p =| Compose q) => Lift1 p e -| Lift1 q e ?

-- * Functors

-- ** Products

-- *** Hask

instance Functor (,) where
  fmap f = Nat (Arrow.first f)

instance Functor ((,) a) where
  fmap = Arrow.second

-- *** Constraint

infixr 2 &

-- needed because we can't partially apply (,) in the world of constraints
class (p, q) => p & q
instance (p, q) => p & q

-- Natural transformations form a category, using parametricity as a (stronger) proxy for naturality

instance Functor (&) where
  fmap f = Nat $ Sub $ Dict \\ f

instance Functor ((&) p) where
  fmap p = Sub $ Dict \\ p

-- ** Coproducts

-- *** Hask

instance Functor Either where
  fmap f = Nat (Arrow.left f)

-- ** Homs

-- *** Hask
instance Functor ((->) e) where
  fmap = (.)

-- ** Constraint

instance Contravariant (:-) where
  contramap f = Nat $ dimap Self runSelf (lmap f)

-- * Misc

instance Functor (Either e) where
  fmap = Arrow.right

-- ** Lens esoterica

data Via (a :: x) (b :: x) (s :: x) (t :: x) where
  Via :: (s ~> a) -> (b ~> t) -> Via a b s t

instance Post Functor ((~>) :: x -> x -> *) => Functor (Via :: x -> x -> x -> x -> *) where
  fmap f = nat3 $ \(Via sa bt) -> Via (fmap1 f sa) bt

instance Post Contravariant ((~>) :: x -> x -> *) => Contravariant (Via :: x -> x -> x -> x -> *) where
  contramap f = nat3 $ \(Via sa bt) -> Via (contramap1 f sa) bt

instance Functor ((~>) :: x -> x -> *) => Functor (Via a :: x -> x -> x -> *) where
  fmap f = nat2 $ \(Via sa bt) -> Via sa (first f bt)

instance Contravariant ((~>) :: x -> x -> *) => Contravariant (Via a :: x -> x -> x -> *) where
  contramap f = nat2 $ \(Via sa bt) -> Via sa (lmap f bt)

instance Functor ((~>) :: x -> x -> *) => Functor (Via a b :: x -> x -> *) where
  fmap f = Nat $ \(Via sa bt) -> Via (first f sa) bt

instance Contravariant ((~>) :: x -> x -> *) => Contravariant (Via a b :: x -> x -> *) where
  contramap f = Nat $ \(Via sa bt) -> Via (lmap f sa) bt

instance Post Functor ((~>) :: x -> x -> *) => Functor (Via a b s :: x -> *) where
  fmap f (Via sa bt) = Via sa (fmap1 f bt)

instance Post Contravariant ((~>) :: x -> x -> *) => Contravariant (Via a b s :: x -> *) where
  contramap f (Via sa bt) = Via sa (contramap1 f bt)

-- |
-- @
-- get   = via _Get
-- beget = via _Beget
-- un    = via _Un
-- @
via :: forall (a :: *) (b :: *) (r :: *) (p :: x -> x -> *) (c :: x) (t :: *) (u :: *).
     Category p => (Via a b a b -> Via r (p c c) u t) -> (t -> u) -> r
via l m = case l (Via id id) of
  Via csa dbt -> csa $ m (dbt id)

mapping :: (Functor f, Functor f', Category (Dom f)) => (Via a b a b -> Via a b s t) -> Iso (f s) (f' t) (f a) (f' b)
mapping l = case l (Via id id) of
  Via csa dbt -> dimap (fmap csa) (fmap dbt)

firstly :: (Functor f, Functor f', Category (Dom f)) => (Via a b a b -> Via a b s t) -> Iso (f s x) (f' t y) (f a x) (f' b y)
firstly l = case l (Via id id) of
  Via csa dbt -> dimap (first csa) (first dbt)

lmapping :: (Contravariant f, Contravariant f', Category (Dom f)) => (Via s t s t -> Via s t a b) -> Iso (f s x) (f' t y) (f a x) (f' b y)
lmapping l = case l (Via id id) of
  Via csa dbt -> dimap (lmap csa) (lmap dbt)

swapping :: (Profunctor f, Profunctor f', Category (Dom f), Category (Cod2 f), Category (Cod2 f'))
         => (Via a b a b -> Via a b s t) -> Iso (f a s) (f' b t) (f s a) (f' t b)
swapping l = case l (Via id id) of
  Via csa dbt -> dimap (dimap csa csa) (dimap dbt dbt)

post :: Category (Arr i) => (Via a b a b -> Via a b s t) -> Iso (i ~> s) (j ~> t) (i ~> a) (j ~> b)
post l = case l (Via id id) of
  Via csa dbt -> dimap (csa .) (dbt .)

pre :: Category (Arr i) => (Via a b a b -> Via a b s t) -> Iso (a ~> i) (b ~> j) (s ~> i) (t ~> j)
pre l = case l (Via id id) of
  Via csa dbt -> dimap (. csa) (. dbt)

-- * The @Hom@ of an (unenriched) category explicitly as a Profunctor

newtype Self a b = Self { runSelf :: a ~> b }
_Self = dimap runSelf Self

instance Category ((~>) :: x -> x -> *) => Contravariant (Self :: x -> x -> *) where
  contramap f = Nat (_Self (.f))

instance Category (Arr a) => Functor (Self a) where
  fmap g (Self h) = Self (g . h)

instance Precartesian (Arr a) => Semimonoidal (Self a :: x -> *) where
  ap2 (ea, eb) = Self (runSelf ea &&& runSelf eb)

instance Cartesian (Arr a) => Monoidal (Self a :: x -> *) where
  ap0 () = Self terminal

instance (Precartesian (Arr a), Semigroup b) => Semigroup (Self a b) where
  mult = multM

instance (Cartesian (Arr a), Monoid b) => Monoid (Self a b) where
  one = oneM


instance Contravariant (->) where
  contramap f = Nat (. f)

instance Contravariant ((~>)::j->j-> *) => Contravariant (Nat::(i->j)->(i->j)-> *) where
  contramap (Nat f) = Nat $ \g -> Nat $ lmap f $ runNat g

instance Contravariant Tagged where
  contramap _ = Nat (_Tagged id)

instance Contravariant (Const2 k) where
  contramap _ = _Const id

-- | Get is the Yoneda embedding C -> [ C^op, Set]
--
-- How? We can view it as a functor from C -> [ C^op X 1, Set ] with the latter embedded in Prof.
--
-- Where does the 1 come from? We use the existence of Contravariance and Covariance in all arguments to make a
-- category where every object is the same as long as the kind chosen has either an initial or a terminal object.
-- But get is polymorphic in the choice of kind for the 'b' parameter, making it possible to choose it to be anything
-- you want.
newtype Get r a b = Get { runGet :: a ~> r }
_Get = dimap runGet Get

instance Category ((~>) :: i -> i -> *) => Functor (Get :: i -> i -> k -> *) where
  fmap f = nat2 $ _Get (f .)

instance Category (Arr r) => Contravariant (Get r) where
  contramap f = Nat (_Get (. f))

instance Contravariant (Get r a) where
  contramap _ = _Get id

instance Functor (Get r a) where
  fmap _ = _Get id

get :: (Category c, c ~ (~>)) => (Get a a a -> Get a s s) -> c s a
get l = runGet $ l (Get id)
-- get = via _Get

-- | Beget is the contravariant Yoneda embedding. C^op -> [C, Set]
--
-- we can view it as a functor from C^op -> [ 1^op X C, Set ] with the latter embedded in Prof.
newtype Beget r a b = Beget { runBeget :: r ~> b }
_Beget = dimap runBeget Beget

instance Category ((~>) :: i -> i -> *) => Contravariant (Beget :: i -> k -> i -> *) where
  contramap f = nat2 $ _Beget (. f)

instance Functor (Beget r) where
  fmap _ = Nat $ _Beget id

instance Contravariant (Beget r) where
  contramap _ = Nat $ _Beget id

instance Category ((~>) :: i -> i -> *) => Functor (Beget (r :: i) (a :: k)) where
  fmap f = _Beget (f .)

beget :: (Category c, c ~ (~>)) => (Beget b b b -> Beget b t t) -> c b t
beget l = runBeget $ l (Beget id)
-- beget = via _Beget

(#) :: (Beget b b b -> Beget b t t) -> b -> t
(#) = beget

-- * Un

-- signatures needed to require endoprofunctors
newtype Un (p::i->i->j) (a::i) (b::i) (s::i) (t::i) = Un { runUn :: p t s ~> p b a }
_Un = dimap runUn Un

instance (Category ((~>)::j->j-> *), Post Functor p) => Contravariant (Un (p::i->i->j) a b) where
  contramap f = Nat $ _Un $ dimap Self runSelf $ lmap (fmap1 f)

instance (Category ((~>)::j->j-> *), Post Contravariant p) => Functor (Un (p::i->i->j) a b) where
  fmap f = Nat $ _Un $ dimap Self runSelf $ lmap (contramap1 f)

instance (Category ((~>)::j->j-> *), Contravariant p) => Functor (Un (p::i->i->j) a b s) where
  fmap g = _Un $ dimap Self runSelf $ lmap (lmap g)

instance (Category ((~>)::j->j-> *), Functor p) => Contravariant (Un (p::i->i->j) a b s) where
  contramap f = _Un $ dimap Self runSelf $ lmap (first f)

un :: (Un p a b a b -> Un p a b s t) -> p t s -> p b a
un l = runUn $ l (Un id)
-- un = via _Un

class (Contravariant p, Functor p) => Phantom p
instance (Contravariant p, Functor p) => Phantom p

class (Bifunctor p, Profunctor (Cod2 p), Category (Cod2 p)) => Semitensor p where
  associate :: Iso (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))

instance Semitensor (,) where
  associate   = dimap (\((a,b),c) -> (a,(b,c)))
                      (\(a,(b,c)) -> ((a,b),c))

instance Semitensor Either where
  associate = dimap hither yon where
    hither (Left (Left a)) = Left a
    hither (Left (Right b)) = Right (Left b)
    hither (Right c) = Right (Right c)
    yon (Left a) = Left (Left a)
    yon (Right (Left b)) = Left (Right b)
    yon (Right (Right c)) = Right c

instance Semitensor (&) where
  associate   = dimap (Sub Dict) (Sub Dict)

type family I (p :: x -> x -> x) :: x

-- tensor for a monoidal category
class Semitensor p => Tensor (p :: x -> x -> x) where
  type Tensorable (p :: x -> x -> x) :: x -> Constraint
  type Tensorable p = Const (() :: Constraint)
  
  lambda :: Tensorable p a => Iso (p (I p) a) (p (I p) a) a a
  rho    :: Tensorable p a => Iso (p a (I p)) (p a (I p)) a a

lambda1 :: forall a p x. (Tensor p, Post (Tensorable p) a) => Iso (p (I p) (a x)) (p (I p) (a x)) (a x) (a x)
lambda1 = case limDict :: Dict (Compose (Tensorable p) a x) of Dict -> lambda

rho1 :: forall a p x. (Tensor p, Post (Tensorable p) a) => Iso (p (a x) (I p)) (p (a x) (I p)) (a x) (a x)
rho1 = case limDict :: Dict (Compose (Tensorable p) a x) of Dict -> rho

type instance I (,) = ()
instance Tensor (,) where
  lambda = dimap (\((), a) -> a) ((,) ())
  rho    = dimap (\(a, ()) -> a) (\a -> (a, ()))

type instance I Either = Void
instance Tensor Either where
  lambda = dimap (\(Right a) -> a) Right
  rho = dimap (\(Left a) -> a) Left

type instance I (&) = (() :: Constraint)
instance Tensor (&) where
  lambda      = dimap (Sub Dict) (Sub Dict)
  rho         = dimap (Sub Dict) (Sub Dict)

instance Semitensor p => Semitensor (Lift1 p) where
  associate   = dimap
    (Nat $ _Lift $ fmap1 (beget _Lift) . get associate . first (get _Lift))
    (Nat $ _Lift $ first (beget _Lift) . beget associate . fmap1 (get _Lift))

type instance I (Lift1 p) = Const1 (I p)
instance Tensor p => Tensor (Lift1 p) where
  type Tensorable (Lift1 p) = Post (Tensorable p)
  lambda = dimap (Nat $ lmap (first (get _Const) . get _Lift) (get lambda1))
                 (Nat $ fmap1 (beget _Lift . first (beget _Const)) (beget lambda1))
  rho = dimap (Nat $ lmap (fmap1 (get _Const) . get _Lift) (get rho1))
              (Nat $ fmap1 (beget _Lift . fmap1 (beget _Const)) (beget rho1))

instance Semitensor p => Semitensor (Lift2 p) where
  associate   = dimap
    (Nat $ _Lift $ fmap1 (beget _Lift) . get associate . first (get _Lift))
    (Nat $ _Lift $ first (beget _Lift) . beget associate . fmap1 (get _Lift))

type instance I (Lift2 p) = Const2 (I p)
instance Tensor p => Tensor (Lift2 p) where
  type Tensorable (Lift2 p) = Post (Tensorable p)
  lambda = dimap
    (Nat $ lmap (first (get _Const) . get _Lift) (get lambda1))
    (Nat $ fmap1 (beget _Lift . first (beget _Const)) (beget lambda1))
  rho = dimap (Nat $ lmap (fmap1 (get _Const) . get _Lift) (get rho1))
              (Nat $ fmap1 (beget _Lift . fmap1 (beget _Const)) (beget rho1))

instance Semitensor p => Semitensor (LiftC p) where
  associate   = dimap
    (Nat $ _Lift $ fmap1 (beget _Lift) . get associate . first (get _Lift))
    (Nat $ _Lift $ first (beget _Lift) . beget associate . fmap1 (get _Lift))

type instance I (LiftC p) = ConstC (I p)
instance Tensor p => Tensor (LiftC p) where
  type Tensorable (LiftC p) = Post (Tensorable p)
  lambda = dimap
    (Nat $ lmap (first (get _Const) . get _Lift) (get lambda1))
    (Nat $ fmap1 (beget _Lift . first (beget _Const)) (beget lambda1))
  rho = dimap (Nat $ lmap (fmap1 (get _Const) . get _Lift) (get rho1))
              (Nat $ fmap1 (beget _Lift . fmap1 (beget _Const)) (beget rho1))

-- * Internal hom of a closed category

class (Profunctor (Internal k), Category k) => Closed (k :: i -> i -> *)  where
  iota :: Iso (Internal k (I (Internal k)) a) (Internal k (I (Internal k)) b) a b
  default iota :: (CCC k, Curryable (*) b, Tensorable (*) b, Tensorable (*) (Internal k (I (*)) a)) 
               => Iso (Internal k (I (Internal k)) a) (Internal k (I (Internal k)) b) a b
  iota = dimap (apply . beget rho) (curry (get rho))

  jot  :: I (Internal k) ~> Internal k a a
  default jot :: (CCC k, Tensorable (*) a) => I (Internal k) ~> Internal k a a
  jot = curry (get lambda)

type instance I (->) = ()
type instance I (|-) = (() :: Constraint)

instance Closed (->)
instance Closed (:-)
instance Closed (Nat :: (i -> *) -> (i -> *) -> *)

-- instance Closed (Nat :: (i -> j -> *) -> (i -> j -> *) -> *)


-- symmetric monoidal category
class Bifunctor p => Symmetric p where
  swap :: p a b ~> p b a

instance Symmetric (,) where
  swap (a,b) = (b, a)

instance Symmetric (&) where
  swap = Sub Dict

instance Symmetric Either where
  swap = either Right Left

instance Symmetric p => Symmetric (Lift1 p) where
  swap = Nat $ _Lift swap

instance Symmetric p => Symmetric (Lift2 p) where
  swap = Nat $ _Lift swap

instance Symmetric p => Symmetric (LiftC p) where
  swap = Nat $ _Lift swap

class One ~ t => Terminal (t :: i) | i -> t where
  type One :: i
  terminal :: a ~> t

instance Terminal () where
  type One = ()
  terminal _ = ()

-- we can only offer the terminal object for Nat :: (i -> *), not Nat :: (i -> j)
instance Terminal t => Terminal (Const1 t) where
  type One = Const1 One
  terminal = Nat (beget _Const . terminal)

instance Terminal t => Terminal (Const2 t) where
  type One = Const2 One
  terminal = Nat (beget _Const . terminal)

instance Terminal (() :: Constraint) where
  type One = (() :: Constraint)
  terminal = Constraint.top

instance Terminal (ConstC ()) where
  type One = ConstC ()
  terminal = Nat (beget _Const . terminal)

class Zero ~ t => Initial (t :: i) | i -> t where
  type Zero :: i
  initial :: t ~> a

instance Initial Void where
  type Zero = Void
  initial = absurd

-- we can only offer the initial object for Nat :: (i -> *), not Nat :: (i -> j)
instance Initial i => Initial (Const1 i) where
  type Zero = Const1 Zero
  initial = Nat $ initial . get _Const

instance Initial i => Initial (Const2 i) where
  type Zero = Const2 Zero
  initial = Nat $ initial . get _Const

instance Initial (() ~ Bool) where
  type Zero = () ~ Bool
  initial = Constraint.bottom

instance Initial i => Initial (ConstC i) where
  type Zero = ConstC Zero
  initial = Nat $ initial . get _Const

infixl 7 *

-- | This is factored out of Precartesian so that we can also use it for copowers/tensors
type family Copower :: i -> j -> j
type (*) = (Copower :: i -> i -> i) -- (*) is a self-copower

class (h ~ (~>), Symmetric ((*)::i->i->i), Semitensor ((*)::i->i->i)) => Precartesian (h :: i -> i -> *) | i -> h where
  fst   :: forall (a::i) (b::i). a * b ~> a
  snd   :: forall (a::i) (b::i). a * b ~> b
  (&&&) :: forall (a::i) (b::i) (c::i). (a ~> b) -> (a ~> c) -> a ~> b * c

class    (h ~ (~>), Tensor ((*)::i->i->i), Terminal (I ((*)::i->i->i)), Precartesian h) => Cartesian (h ::i->i-> *) | i -> h
instance (h ~ (~>), Tensor ((*)::i->i->i), Terminal (I ((*)::i->i->i)), Precartesian h) => Cartesian (h ::i->i-> *)

type instance Copower = (,)
instance Precartesian (->) where
  fst   = Prelude.fst
  snd   = Prelude.snd
  (&&&) = (Arrow.&&&)

type instance Copower = (&)
instance Precartesian (:-) where
  fst = Sub Dict
  snd = Sub Dict
  p &&& q = Sub $ Dict \\ p \\ q

type instance Copower = Lift (,)
instance Precartesian (Nat :: (i -> *) -> (i -> *) -> *) where
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ Lift . (f &&& g)

type instance Copower = Lift2 (*)
instance Precartesian (Nat :: (i -> j -> *) -> (i -> j -> *) -> *) where
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ beget _Lift . (f &&& g)

type instance Copower = LiftC (&)
instance Precartesian (Nat :: (i -> Constraint) -> (i -> Constraint) -> *) where
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ beget _Lift . (f &&& g)

infixl 6 +
class (h ~ (~>), Symmetric ((+)::i->i->i), Semitensor ((+)::i->i->i)) => Precocartesian (h :: i -> i -> *) | i -> h where
  type (+) :: i -> i -> i
  inl    :: forall (a :: i) (b :: i). a ~> a + b
  inr    :: forall (a :: i) (b :: i). b ~> a + b
  (|||)  :: forall (a :: i) (b :: i) (c :: i). (a ~> c) -> (b ~> c) -> a + b ~> c

class    (h ~ (~>), Tensor ((+)::i->i->i), Initial (I ((+)::i->i->i)), Precocartesian h) => Cocartesian (h ::i->i-> *) | i -> h
instance (h ~ (~>), Tensor ((+)::i->i->i), Initial (I ((+)::i->i->i)), Precocartesian h) => Cocartesian (h ::i->i-> *)

instance Precocartesian (->) where
  type (+) = Either
  inl = Left
  inr = Right
  (|||) = either

instance Precocartesian (Nat :: (i -> *) -> (i -> *) -> *) where
  type (+) = Lift1 (+)
  inl = Nat (beget _Lift . inl)
  inr = Nat (beget _Lift . inr)
  Nat f ||| Nat g = Nat $ (f ||| g) . get _Lift

instance Precocartesian (Nat :: (i -> j -> *) -> (i -> j -> *) -> *) where
  type (+) = Lift2 (+)
  inl = Nat (beget _Lift . inl)
  inr = Nat (beget _Lift . inr)
  Nat f ||| Nat g = Nat $ (f ||| g) . get _Lift

-- * Factoring

factor :: (Post Functor (f :: j -> i -> i), Precocartesian (Cod2 f)) => f e b + f e c ~> f e (b + c)
factor = fmap1 inl ||| fmap1 inr

-- TODO: play fancy combinator games to figure out how to make

-- distributive always a getter capable of factoring, while make it only require an instance
-- to get the inverses.
class (Cartesian k, Cocartesian k) => Distributive (k :: i -> i -> *) | i -> k where
  distribute :: forall (a :: i) (b :: i) (c :: i) (a' :: i) (b' :: i) (c' :: i).
             Iso ((a * b) + (a * c)) ((a' * b') + (a' * c'))
                 (a * (b + c))       (a' * (b' + c'))

instance Distributive (->) where
  distribute = dimap factor $ \case
    (a, Left b) -> Left (a, b)
    (a, Right c) -> Right (a, c)

instance Distributive (Nat :: (i -> *) -> (i -> *) -> *) where
  distribute = dimap factor $ Nat $ \case
    Lift (a, Lift (Left b)) -> Lift (Left (Lift (a, b)))
    Lift (a, Lift (Right b)) -> Lift (Right (Lift (a, b)))

instance Distributive (Nat :: (i -> j -> *) -> (i -> j -> *) -> *) where
  distribute = dimap factor $ Nat $ Nat $ \case
     Lift2 (Lift (a, Lift2 (Lift (Left b)))) -> Lift2 (Lift (Left (Lift2 (Lift (a, b)))))
     Lift2 (Lift (a, Lift2 (Lift (Right b)))) -> Lift2 (Lift (Right (Lift2 (Lift (a, b)))))

-- gives us a notion of a closed category when applied to the exponential
--
-- this is just another convenient indexed adjunction with the args flipped around
-- type family Curryable (p :: k -> i -> j) (a :: k) :: Constraint
-- type instance Curryable (a :: *) = (() :: Constraint)
-- type instance Curryable (a :: Constraint) = (() :: Constraint)
-- type instance Curryable (a :: i -> *) = Functor a

-- p has some notion of association we'd need poly kinds to talk about properly
class Curried (p :: k -> i -> j) (e :: i -> j -> k) | p -> e, e -> p where
  type Curryable (p :: k -> i -> j) :: k -> Constraint
  type Curryable p = Const (() :: Constraint)

  {-# MINIMAL (curry, uncurry) | (apply, unapply) #-}

  curry :: Curryable p a => (p a b ~> c) -> a ~> e b c
  default curry :: (Post Functor e, Category (Cod2 e), Category (Cod2 p), Curryable p a) => (p a b ~> c) -> a ~> e b c
  curry q = fmap1 q . unapply

  uncurry :: (a ~> e b c) -> p a b ~> c
  default uncurry :: (Functor p, Category (Cod2 e), Category (Cod2 p)) => (a ~> e b c) -> p a b ~> c
  uncurry p = apply . first p

  apply :: p (e a b) a ~> b
  default apply :: Category (Cod2 e) => p (e a b) a ~> b
  apply = uncurry id

  unapply :: Curryable p a => a ~> e b (p a b)
  default unapply :: (Category (Cod2 p), Curryable p a) => a ~> e b (p a b)
  unapply = curry id

curried :: (Curried p e, Curryable p a) => Iso (p a b ~> c) (p a' b' ~> c') (a ~> e b c) (a' ~> e b' c')
curried = dimap curry uncurry

ccc :: (Category (Cod2 p), Symmetric p, Curried p e, Curryable p a) => Iso (p i a ~> b) (p i' a' ~> b') (a ~> e i b) (a' ~> e i' b')
ccc = dimap (. swap) (. swap) . curried

-- e.g. (Lan f g ~> h) is isomorphic to (g ~> h · f)

-- Cocurried :: (k -> k1 -> k2) -> (k2 -> k -> k1) -> Constraint

class Cocurried (f :: i -> j -> k) (u :: k -> i -> j) | f -> u , u -> f where
  type Cocurryable (u :: k -> i -> j) :: k -> Constraint
  type Cocurryable p = Const (() :: Constraint)

  cocurry   :: (f a b ~> c) -> b ~> u c a
  uncocurry :: Cocurryable u c => (b ~> u c a) -> f a b ~> c

cocurried :: (Cocurried f u, Cocurryable u c') => Iso (f a b ~> c) (f a' b' ~> c') (b ~> u c a) (b' ~> u c' a')
cocurried = dimap cocurry uncocurry

-- * CCCs

class
  ( Cartesian k
  , Closed k
  , Curried (*) (Internal k)
  , I (Internal k) ~ I (*)
  , Curryable (*) (I (Internal k))
  ) => CCC (k :: x -> x -> *) | x -> k

instance Curried (,) (->) where
  curry = Prelude.curry
  uncurry = Prelude.uncurry

instance CCC (->)

instance (,) e -| (->) e where
  adj = ccc

instance CCC (Nat :: (i -> *) -> (i -> *) -> *)

-- semimonoidal functors preserve the structure of our pretensor and take semimonoid objects to semimonoid objects
class (Precartesian ((~>) :: x -> x -> *), Precartesian ((~>) :: y -> y -> *), Functor f) => Semimonoidal (f :: x -> y) where
  ap2 :: f a * f b ~> f (a * b)

-- monoidal functors preserve the structure of our tensor and take monoid objects to monoid objects
--
-- These are technically 'cartesian' functors, we we only define them over cartesian categories
class (Cartesian ((~>) :: x -> x -> *), Cartesian ((~>) :: y -> y -> *), Semimonoidal f) => Monoidal (f :: x -> y) where
  ap0 :: One ~> f One

instance Semimonoidal Dict where
  ap2 (Dict, Dict) = Dict

instance Monoidal Dict where
  ap0 () = Dict

instance Semigroup (Dict m) where
  mult (Dict, Dict) = Dict

instance Monoid m => Monoid (Dict m) where
  one = oneM

-- lift applicatives for Hask
--
-- instance Base.Applicative f => Monoidal f where
--   ap0 = Base.pure
--   ap2 = uncurry $ Base.liftA2 (,)

ap2Applicative :: Base.Applicative f => f a * f b -> f (a * b)
ap2Applicative = uncurry $ Base.liftA2 (,)

instance Semimonoidal ((:-) f) where
  ap2 = uncurry (&&&)

instance Monoidal ((:-) f) where
  ap0 () = terminal

instance Semigroup (f :- m) where -- every m is a semimonoid
  mult = multM

instance Monoid m => Monoid (f :- m) where
  one = oneM

{-
instance Semimonoidal (Lift1 (->) f) where
  ap2 = get zipR1

instance Monoidal (Lift1 (->) f) where
  ap0 = curry fst

instance Semigroup m => Semigroup (Lift1 (->) f m) where
  mult = multM

instance Monoid m => Monoid (Lift1 (->) f m) where
  one = oneM
-}

-- instance Monoidal (LiftC (|-) f) where
--  ap0 = curry fst
--  ap2 = get zipR

instance Semimonoidal ((|-) f) where
  ap2 = get zipR

instance Monoidal ((|-) f) where
  ap0 = curry fst

-- instance Semigroup m => Semigroup (f |- m) where mult = multM -- all constraints are semimonoids!

instance Monoid m => Monoid (f |- m) where
  one = oneM

instance Semimonoidal (Nat f :: (i -> *) -> *) where
  ap2 = uncurry (&&&)

instance Monoidal (Nat f :: (i -> *) -> *) where
  ap0 () = terminal

instance Semimonoidal (Nat f :: (i -> Constraint) -> *) where
  ap2 = uncurry (&&&)

instance Monoidal (Nat f :: (i -> Constraint) -> *) where
  ap0 () = terminal

instance (Semimonoidal (Nat f), Semigroup m) => Semigroup (Nat f m) where
  mult = multM

instance (Monoidal (Nat f), Monoid m) => Monoid (Nat f m) where
  one = oneM

-- inherited from base
instance Semimonoidal (Tagged s) where
  ap2 = Tagged . bimap unTagged unTagged

instance Monoidal (Tagged s) where
  ap0  = Tagged

instance Semigroup m => Semigroup (Tagged s m) where
  mult = Tagged . mult . bimap unTagged unTagged

instance Monoid m => Monoid (Tagged s m) where
  one = Tagged . one

instance Precartesian ((~>) :: i -> i -> *) => Semimonoidal (Proxy :: i -> *) where
  ap2 (Proxy, Proxy) = Proxy

instance Cartesian ((~>) :: i -> i -> *) => Monoidal (Proxy :: i -> *) where
  ap0 () = Proxy

-- instance Monoid (Proxy a) -- from base

-- * Monads over our kind-indexed categories

class Semimonoidal (m :: x -> x) => Semimonad (m :: x -> x) where
  {-# MINIMAL join | bind #-}
  join :: m (m a) ~> m a
  join = bind id

  bind :: Semimonad m => (a ~> m b) ~> m a ~> m b
  bind f = join . fmap f

-- todo: prove join must respect this?
class (Monoidal m, Semimonad m) => Monad m
instance (Monoidal m, Semimonad m) => Monad m

-- instance (Semimonoidal m, Base.Monad m) => Semimonad m where
-- instance (Monoidal m, Base.Monad m) => Monad m where
--   join = Monad.join

-- * Comonoidal functors between cocartesian categories

class (Precocartesian ((~>) :: x -> x -> *), Precocartesian ((~>) :: y -> y -> *), Functor f) => Cosemimonoidal (f :: x -> y) where
  op2 :: f (a + b) ~> f a + f b

class (Cocartesian ((~>) :: x -> x -> *), Cocartesian ((~>) :: y -> y -> *), Cosemimonoidal f) => Comonoidal (f :: x -> y) where
  op0 :: f Zero ~> Zero

instance Cosemimonoidal ((,) e) where
  op2 (e,ab) = bimap ((,) e) ((,) e) ab

instance Comonoidal ((,) e) where
  op0 = snd

instance Cosemigroup m => Cosemigroup (e, m) where
  comult = comultOp

instance Comonoid m => Comonoid (e, m) where
  zero = zeroOp

instance Cosemimonoidal Base.Identity where
  op2 = bimap Base.Identity Base.Identity . Base.runIdentity

instance Comonoidal Base.Identity where
  op0 = Base.runIdentity

instance Cosemigroup m => Cosemigroup (Base.Identity m) where
  comult = comultOp

instance Comonoid m => Comonoid (Base.Identity m) where
  zero = zeroOp

-- lift all of these through Lift? its a limit

-- instance Cosemimonoidal p => Cosemimonoidal (Lift1 p e) where
instance Cosemimonoidal (Lift1 (,) e) where
  op2 = Nat $ Lift . bimap Lift Lift . op2 . fmap lower . lower

instance Comonoidal (Lift1 (,) e) where
  op0 = snd

instance Cosemigroup m => Cosemigroup (Lift1 (,) e m) where
  comult = comultOp

instance Comonoid m => Comonoid (Lift1 (,) e m) where
  zero = zeroOp

instance Cosemimonoidal (Tagged s) where
  op2 = bimap Tagged Tagged . unTagged

instance Comonoidal (Tagged s) where
  op0 = unTagged

instance Cosemigroup m => Cosemigroup (Tagged s m) where
  comult = comultOp

instance Comonoid m => Comonoid (Tagged s m) where
  zero = zeroOp

-- * Identity functors

class (f -| f, Id ~ f) => Identity (f :: i -> i) | i -> f where
  type Id :: i -> i
  _Id :: Iso (f a) (f a') a a'

instance Identity Base.Identity where
  type Id = Base.Identity
  _Id = dimap Base.runIdentity Base.Identity

instance Functor Base.Identity where
  fmap = Base.fmap

instance Base.Identity -| Base.Identity where
  adj = un (mapping _Id . lmapping _Id)

-- * Id1 = Identity for Nat (i -> *)
newtype Id1 (f :: i -> *) (a :: i) = Id1 { runId1 :: f a }
_Id1 = dimap runId1 Id1

instance Identity Id1 where
  type Id = Id1
  _Id = dimap (Nat runId1) (Nat Id1)

instance Functor f => Functor (Id1 f) where
  fmap = _Id1 . fmap

instance Cosemimonad Id1 where
  duplicate = Nat Id1

instance Comonad Id1 where
  extract = Nat runId1

instance Semimonoidal Id1 where
  ap2 = Nat $ \(Lift (Id1 x, Id1 y)) -> Id1 (Lift (x, y))

instance Monoidal Id1 where
  ap0 = Nat Id1

instance Semigroup m => Semigroup (Id1 m) where
  mult = multM

instance Monoid m => Monoid (Id1 m) where
  one = oneM

instance Semimonad Id1 where
  join = Nat runId1

instance Monad Id1

instance Cosemimonoidal Id1 where
  op2 = Nat $ \(Id1 (Lift ea)) -> Lift (bimap Id1 Id1 ea)

instance Comonoidal Id1 where
  op0 = Nat runId1

instance Cosemigroup m => Cosemigroup (Id1 m) where
  comult = comultOp

instance Comonoid m => Comonoid (Id1 m) where
  zero = zeroOp

instance Id1 -| Id1 where
  adj = un (mapping _Id . lmapping _Id)

instance Contravariant f => Contravariant (Id1 f) where
  contramap = _Id1 . contramap

instance Functor Id1 where
  fmap = _Id

instance Semimonoidal f => Semimonoidal (Id1 f) where
  ap2 = Id1 . ap2 . bimap runId1 runId1

instance Monoidal f => Monoidal (Id1 f) where
  ap0 = Id1 . ap0

instance Cosemimonoidal f => Cosemimonoidal (Id1 f) where
  op2 = bimap Id1 Id1 . op2 . runId1

instance Comonoidal f => Comonoidal (Id1 f) where
  op0 = op0 . runId1

instance (Cosemimonoidal f, Cosemigroup m) => Cosemigroup (Id1 f m) where
  comult = comultOp

instance (Comonoidal f, Comonoid m) => Comonoid (Id1 f m) where
  zero = zeroOp

class c => IdC c
instance c => IdC c

instance Identity IdC where
  type Id = IdC
  _Id = dimap (Sub Dict) (Sub Dict)

instance Functor IdC where
  fmap = _Id

instance IdC -| IdC where
  adj = un (mapping _Id . lmapping _Id)

class Precartesian (Arr m) => Semigroup m where
  mult :: m * m ~> m

-- a monoid object in a cartesian category
class (Semigroup m, Cartesian (Arr m)) => Monoid m where
  one  :: One ~> m

-- monoidal functors take monoids to monoids

oneM :: (Monoidal u, Monoid m) => One ~> u m
oneM = fmap one . ap0

multM :: (Semimonoidal u, Semigroup m) => u m * u m ~> u m
multM = fmap mult . ap2

-- instance Semigroup.Semigroup m => Semigroup m where
--   mult = uncurry Monoid.mappend

-- instance (Semigroup.Semigroup m, Base.Monoid m) => Monoid m where
--   one () = Monoid.mempty

instance Semigroup (Const1 ()) where
  mult = get lambda

instance Monoid (Const1 ()) where
  one = id

instance Semigroup (p :: Constraint) where
  mult = Sub Dict

instance Monoid (() :: Constraint) where
  one = id

mappend :: (Semigroup m, CCC (Arr m), Curryable (*) m) => m ~> m^m
mappend = curry mult

class Precocartesian (Arr m) => Cosemigroup m where
  comult :: m ~> m + m

class (Cosemigroup m, Cocartesian (Arr m)) => Comonoid m where
  zero   :: m ~> Zero

-- opmonoidal functors take comonoids to comonoids

zeroOp :: (Comonoidal f, Comonoid m) => f m ~> Zero
zeroOp = op0 . fmap zero

comultOp :: (Cosemimonoidal f, Cosemigroup m) => f m ~> f m + f m
comultOp = op2 . fmap comult

instance Cosemigroup Void where
  comult = initial

instance Comonoid Void where
  zero = id

instance Semigroup Void where
  mult = fst

instance Cosemigroup (Const1 Void) where
  comult = Nat $ absurd . getConst

instance Comonoid (Const1 Void) where
  zero = id

instance Semigroup (Const1 Void) where
  mult = fst

-- instance Comonoid (Const2 (Const1 Void)) where

class Functor f => Strength f where
  strength :: a * f b ~> f (a * b) -- this should be able to be an arbitrary copower instead

-- instance (Functor f, Base.Functor f) => Strength f where
instance Functor f => Strength (f :: * -> *) where
  strength (a,fb) = fmap ((,) a) fb

-- proposition: all right adjoints on Cartesian categories should be strong
-- strengthR   :: (f -| u, Cartesian (Dom u)) => a * u b ~> u (a * b)
-- costrengthL :: (f -| u, Cartesian (Dom f)) => f (a + b) ~> a + f b

-- what is usually called 'costrength' is more like a 'left strength' or a 'right strength'
-- repurposing this term for a real 'co'-strength
class Functor f => Costrength (f :: x -> x) where
  costrength :: f (a + b) ~> a + f b

instance (Functor f, Base.Traversable f) => Costrength f where
  costrength = Base.sequence

ap :: (Semimonoidal f, CCC (Dom f), CCC (Cod f), Curryable (*) (f (b ^ a))) => f (b ^ a) ~> f b ^ f a
ap = curry (fmap apply . ap2)

return :: (Monoidal f, Strength f, CCC (Dom f), Tensorable (*) a) => a ~> f a
return = fmap (get lambda . swap) . strength . fmap1 ap0 . beget rho

class (Functor f, Category (Dom f)) => Cosemimonad f where
  {-# MINIMAL (duplicate | extend) #-}
  duplicate :: f a ~> f (f a)
  default duplicate :: Category (Dom f) => f a ~> f (f a)
  duplicate = extend id

  extend :: (f a ~> b) -> f a ~> f b
  extend f = fmap f . duplicate

class Cosemimonad f => Comonad f where
  extract :: f a ~> a

-- * Traditional product categories w/ adjoined identities
data Prod :: (i,j) -> (i,j) -> * where
  Want :: Prod a a
  Have :: (a ~> b) -> (c ~> d) -> Prod '(a,c) '(b,d)

instance (Category ((~>) :: i -> i -> *), Category ((~>) :: j -> j -> *)) => Category (Prod :: (i,j) -> (i,j) -> *) where
  id = Want
  Want . f = f
  f . Want = f
  Have f f' . Have g g' = Have (f . g) (f' . g')

instance (Functor ((~>) a :: i -> *), Functor ((~>) b :: j -> *), ab ~ '(a,b)) => Functor (Prod ab :: (i, j) -> *) where
  fmap Want f = f
  fmap f Want = f
  fmap (Have f g) (Have f' g') = Have (fmap f f') (fmap g g')

instance (Contravariant ((~>) :: i -> i -> *), Contravariant ((~>) :: j -> j -> *)) => Contravariant (Prod :: (i, j) -> (i, j) -> *) where
  contramap Want = id
  contramap (Have f g) = Nat $ \case
    Want       -> Have f g
    Have f' g' -> Have (lmap f f') (lmap g g')

runProd :: forall (a :: i) (b :: i) (c :: j) (d :: j).
           (Category ((~>) :: i -> i -> *), Category ((~>) :: j -> j -> *))
        => Prod '(a,c) '(b,d) -> (a ~> b, c ~> d)
runProd Want       = (id,id)
runProd (Have f g) = (f,g)

runFst
  :: forall (a :: i) (b :: i) (c :: j) (d :: j).
     Category ((~>) :: i -> i -> *)
  => Prod '(a,c) '(b,d) -> a ~> b
runFst Want       = id
runFst (Have f _) = f

runSnd
  :: forall (a :: i) (b :: i) (c :: j) (d :: j).
     Category ((~>) :: j -> j -> *)
  => Prod '(a,c) '(b,d) -> c ~> d
runSnd Want       = id
runSnd (Have _ g) = g

-- Δ -| (*)
diagProdAdj :: forall (a :: i) (b :: i) (c :: i) (a' :: i) (b' :: i) (c' :: i).
   Cartesian ((~>) :: i -> i -> *) =>
   Iso ('(a,a) ~> '(b,c)) ('(a',a') ~> '(b',c')) (a ~> b * c) (a' ~> b' * c')
diagProdAdj = dimap (uncurry (&&&) . runProd) $ \f -> Have (fst . f) (snd . f)

-- (+) -| Δ
sumDiagAdj :: forall (a :: i) (b :: i) (c :: i) (a' :: i) (b' :: i) (c' :: i).
   Cocartesian ((~>) :: i -> i -> *) =>
   Iso (b + c ~> a) (b' + c' ~> a') ('(b,c) ~> '(a,a)) ('(b',c') ~> '(a',a'))
sumDiagAdj = dimap (\f -> Have (f . inl) (f . inr)) (uncurry (|||) . runProd)

-- * Work in progress

infixr 9 |-
-- exponentials for constraints
class p |- q where
  implies :: p :- q

-- convert to and from the internal representation of dictionaries

_Sub :: Iso (p :- q) (p' :- q') (Dict p -> Dict q) (Dict p' -> Dict q')
_Sub = dimap (\pq Dict -> case pq of Sub q -> q) (\f -> Sub $ f Dict)

newtype Magic p q r = Magic ((p |- q) => r)

_Implies :: Iso (p :- q) (p' :- q') (Dict (p |- q)) (Dict (p' |- q'))
_Implies = dimap (reify Dict) (\Dict -> implies) where
  reify :: forall p q r. ((p |- q) => r) -> (p :- q) -> r
  reify k = unsafeCoerce (Magic k :: Magic p q r)

instance Contravariant (|-) where
  contramap f = Nat $ beget _Sub $ un _Implies (. f)

instance Functor ((|-) p) where
  fmap f = beget _Sub $ un _Implies (f .)

--instance (&) =| (|-) where
--  adj1 = ccc

instance (&) p -| (|-) p where
  adj = ccc

instance Curried (&) (|-) where
  apply = applyConstraint where
    applyConstraint :: forall p q. (p |- q & p) :- q
    applyConstraint = Sub $ Dict \\ (implies :: p :- q)
  unapply = unapplyConstraint where
    unapplyConstraint :: p :- q |- (p & q)
    unapplyConstraint = Sub $ get _Implies (Sub Dict)

instance CCC (:-)

-- * The terminal category with one object

data Unit (a :: ()) (b :: ()) = Unit

instance Category Unit where
  id = Unit
  Unit . Unit = Unit

instance Contravariant Unit where
  contramap f = Nat (. f)

instance Functor (Unit a) where
  fmap = (.)

instance Terminal '() where
  type One = '()
  terminal = Unit

instance Initial '() where
  type Zero = '()
  initial = Unit

-- Unit also forms a bifunctor, so you can map forwards/backwards, etc.

instance Functor Unit where
  fmap = contramap . swap -- inverse

instance Contravariant (Unit a) where
  contramap = fmap . swap -- inverse

instance Symmetric Unit where
  swap Unit = Unit


-- * The initial "empty" category

newtype Empty (a :: Void) (b :: Void) = Empty (Empty a b)

instance Category Empty where
  id = Empty id
  (.) (!f0) = spin f0 where
    spin (Empty f) = spin f

instance Symmetric Empty where
  swap (Empty f) = Empty (swap f)

instance Contravariant Empty where
  contramap f = Nat (. f)

instance Functor Empty where
  fmap = contramap . swap

instance Functor (Empty a) where
  fmap = (.)

instance Contravariant (Empty a) where
  contramap = fmap . swap

-- No :: Void -> *
data No (a :: Void)

instance Functor No where
  fmap !_ = Prelude.undefined

-- * More about composition

composed = dimap decompose compose

associateCompose = dimap (Nat (compose . fmap compose . decompose . decompose))
                         (Nat (compose . compose . fmap decompose . decompose))

whiskerComposeL k = Nat $ composed $ runNat k
whiskerComposeR k = Nat $ composed $ fmap (runNat k)
lambdaCompose = dimap (Nat (compose . beget _Id)) (Nat (get _Id . decompose))
rhoCompose = dimap (Nat (fmap (get _Id) . decompose)) (Nat (compose . fmap (beget _Id)))

-- if we can use it this coend based definition works for more things, notably it plays well with Ran/Lan
newtype Compose1 f g a = Compose { getCompose :: f (g a) }

instance Composed (->) where
  type Compose = Compose1
  compose = Compose
  decompose = getCompose

--instance Semitensor Compose1 where
  -- needs a functor on b to decompose
  -- associate = dimap (Nat $ \(Compose1 (Compose1 ax x2by) y2cz) -> Compose1 ax (\x -> Compose1 (x2by x) y2cz))
  --                  (Nat $ \(Compose1 ax x2bcz) -> Compose1 (Compose1 ax (decompose . x2bcz)) id)

newtype Compose2 f g a b = Compose2 { getCompose2 :: f (g a) b }


instance Composed (Nat :: (k -> *) -> (k -> *) -> *) where
  type Compose = Compose2
  compose   = Nat Compose2
  decompose = Nat getCompose2

instance Functor Compose1 where
  fmap f = nat2 $ composed $ runNat f

instance Functor Compose2 where
  fmap f = nat2 $ composed $ runNat f

instance Functor ComposeC where
  fmap f = nat2 $ composed $ runNat f

instance Functor f => Functor (Compose1 f) where
  fmap f = Nat $ composed $ fmap $ runNat f

instance Functor f => Functor (Compose2 f) where
  fmap f = Nat $ composed $ fmap $ runNat f

instance Functor f => Functor (ComposeC f) where
  fmap f = Nat $ composed $ fmap $ runNat f

instance Contravariant f => Contravariant (Compose1 f) where
  contramap f = Nat $ composed $ contramap $ runNat f

instance Contravariant f => Contravariant (Compose2 f) where
  contramap f = Nat $ composed $ contramap $ runNat f

instance Contravariant f => Contravariant (ComposeC f) where
  contramap f = Nat $ composed $ contramap $ runNat f

instance (Functor f, Functor g) => Functor (Compose1 f g) where
  fmap = composed . fmap . fmap

instance (Functor f, Functor g) => Functor (Compose2 f g) where
  fmap = composed . fmap . fmap

instance (Functor f, Functor g) => Functor (ComposeC f g) where
  fmap = composed . fmap . fmap

instance (Semimonoidal f, Semimonoidal g) => Semimonoidal (Compose1 f g) where
  ap2 = compose . fmap ap2 . ap2 . bimap decompose decompose

instance (Semimonoidal f, Semimonoidal g) => Semimonoidal (Compose2 f g) where
  ap2 = compose . fmap ap2 . ap2 . bimap decompose decompose

instance (Semimonoidal f, Semimonoidal g) => Semimonoidal (ComposeC f g) where
  ap2 = compose . fmap ap2 . ap2 . bimap decompose decompose

instance (Monoidal f, Monoidal g) => Monoidal (Compose1 f g) where
  ap0 = compose . fmap ap0 . ap0

instance (Monoidal f, Monoidal g) => Monoidal (Compose2 f g) where
  ap0 = compose . fmap ap0 . ap0

instance (Monoidal f, Monoidal g) => Monoidal (ComposeC f g) where
  ap0 = compose . fmap ap0 . ap0

instance (Cosemimonoidal f, Cosemimonoidal g) => Cosemimonoidal (Compose1 f g) where
  op2 = bimap compose compose . op2 . fmap op2 . decompose

instance (Cosemimonoidal f, Cosemimonoidal g) => Cosemimonoidal (Compose2 f g) where
  op2 = bimap compose compose . op2 . fmap op2 . decompose

instance (Cosemimonoidal f, Cosemimonoidal g) => Cosemimonoidal (ComposeC f g) where
  op2 = bimap compose compose . op2 . fmap op2 . decompose

instance (Comonoidal f, Comonoidal g) => Comonoidal (Compose1 f g) where
  op0 = op0 . fmap op0 . decompose

instance (Comonoidal f, Comonoidal g) => Comonoidal (Compose2 f g) where
  op0 = op0 . fmap op0 . decompose

instance (Comonoidal f, Comonoidal g) => Comonoidal (ComposeC f g) where
  op0 = op0 . fmap op0 . decompose

instance (Semimonoidal f, Semimonoidal g, Semigroup m) => Semigroup (Compose1 f g m) where
  mult = compose . fmap (fmap mult . ap2) . ap2 . bimap decompose decompose

instance (Semimonoidal f, Semimonoidal g, Semigroup m) => Semigroup (Compose2 f g m) where
  mult = compose . fmap (fmap mult . ap2) . ap2 . bimap decompose decompose

instance (Monoidal f, Monoidal g, Monoid m) => Monoid (Compose1 f g m) where
  one = compose . fmap (fmap one . ap0) . ap0

instance (Monoidal f, Monoidal g, Monoid m) => Monoid (Compose2 f g m) where
  one = compose . fmap (fmap one . ap0) . ap0

instance (Monoidal f, Monoidal g, Monoid m) => Monoid (ComposeC f g m) where
  one = compose . fmap (fmap one . ap0) . ap0

instance (Cosemimonoidal f, Cosemimonoidal g, Cosemigroup m) => Cosemigroup (Compose1 f g m) where
  comult = bimap compose compose . op2 . fmap (op2 . fmap comult) . decompose

instance (Cosemimonoidal f, Cosemimonoidal g, Cosemigroup m) => Cosemigroup (Compose2 f g m) where
  comult = bimap compose compose . op2 . fmap (op2 . fmap comult) . decompose

instance (Cosemimonoidal f, Cosemimonoidal g, Cosemigroup m) => Cosemigroup (ComposeC f g m) where
  comult = bimap compose compose . op2 . fmap (op2 . fmap comult) . decompose

instance (Comonoidal f, Comonoidal g, Comonoid m) => Comonoid (Compose1 f g m) where
  zero = op0 . fmap (op0 . fmap zero) . decompose

instance (Comonoidal f, Comonoidal g, Comonoid m) => Comonoid (Compose2 f g m) where
  zero = op0 . fmap (op0 . fmap zero) . decompose

instance (Comonoidal f, Comonoidal g, Comonoid m) => Comonoid (ComposeC f g m) where
  zero = op0 . fmap (op0 . fmap zero) . decompose

-- composition of adjunctions

instance (f -| g, f' -| g', Category (Dom f), Category (Cod f)) => Compose1 f' f -| Compose1 g g' where
  adj = dimap (fmap1 compose . get adj . get adj . lmap compose)
              (lmap decompose . beget adj . beget adj . fmap1 decompose)

instance (f -| g, f' -| g', Category (Dom f), Category (Cod f)) => Compose1 f' f -| Compose2 g g' where
  adj = dimap (fmap1 compose . get adj . get adj . lmap compose)
              (lmap decompose . beget adj . beget adj . fmap1 decompose)

instance (f -| g, f' -| g', Category (Dom f), Category (Cod f)) => Compose1 f' f -| ComposeC g g' where
  adj = dimap (fmap1 compose . get adj . get adj . lmap compose)
              (lmap decompose . beget adj . beget adj . fmap1 decompose)

-- a semigroupoid/semicategory looks like a "self-enriched" profunctor
-- when we put no other constraints on p

class    (Profunctor p, p ~ (~>)) => Semicategory p
instance (Profunctor p, p ~ (~>)) => Semicategory p

-- * Work in progress

-- Nat :: (i -> *) -> (i -> *) -> * is tensored. (Copowered over Hask)
data Copower1 x f a = Copower x (f a)
type instance Copower = Copower1

instance Functor Copower1 where
  fmap f = nat2 $ \(Copower x fa) -> Copower (f x) fa

instance Functor (Copower1 x) where
  fmap f = Nat $ \(Copower x fa) -> Copower x (runNat f fa)

instance Functor f => Functor (Copower1 x f) where
  fmap f (Copower x fa) = Copower x (fmap f fa)

instance Contravariant f => Contravariant (Copower1 x f) where
  contramap f (Copower x fa) = Copower x (contramap f fa)

instance Curried Copower1 Nat where
  curry f a = Nat $ \e -> runNat f (Copower a e)
  uncurry f = Nat $ \(Copower a e) -> runNat (f a) e

data Copower2 x f a b = Copower2 x (f a b)
type instance Copower = Copower2

instance Functor Copower2 where
  fmap f = nat3 $ \(Copower2 x fab) -> Copower2 (f x) fab

instance Functor (Copower2 x) where
  fmap f = nat2 $ \(Copower2 x fab) -> Copower2 x (runNat2 f fab)

instance Functor f => Functor (Copower2 x f) where
  fmap f = Nat $ \(Copower2 x fab) -> Copower2 x (first f fab)

instance Post Functor f => Functor (Copower2 x f a) where
  fmap f (Copower2 x fab) = Copower2 x (fmap1 f fab)

instance Contravariant f => Contravariant (Copower2 x f) where
  contramap f = Nat $ \(Copower2 x fab) -> Copower2 x (lmap f fab)

instance Post Contravariant f => Contravariant (Copower2 x f a) where
  contramap f (Copower2 x fab) = Copower2 x (contramap1 f fab)

instance Curried Copower2 Nat where
  curry f a = nat2 $ \b -> runNat2 f (Copower2 a b)
  uncurry f = nat2 $ \(Copower2 a b) -> runNat2 (f a) b

-- Nat :: (i -> j -> *) -> (i -> j -> *) -> * is tensored. (Copowered over Nat :: (i -> *) -> (i -> *) -> *)
data Copower2_1 x f a b = Copower2_1 (x a) (f a b)
type instance Copower = Copower2_1

instance Functor Copower2_1 where
  fmap f = nat3 $ \(Copower2_1 xa fab) -> Copower2_1 (runNat f xa) fab

instance Functor (Copower2_1 x) where
  fmap f = nat2 $ \(Copower2_1 xa fab) -> Copower2_1 xa (runNat2 f fab)

instance (Functor x, Functor f) => Functor (Copower2_1 x f) where
  fmap f = Nat $ \(Copower2_1 xa fab) -> Copower2_1 (fmap f xa) (first f fab)

instance (Contravariant x, Contravariant f) => Contravariant (Copower2_1 x f) where
  contramap f = Nat $ \(Copower2_1 xa fab) -> Copower2_1 (contramap f xa) (lmap f fab)

instance Post Functor f => Functor (Copower2_1 x f a) where
  fmap f (Copower2_1 xa fab) = Copower2_1 xa (fmap1 f fab)

instance Post Contravariant f => Contravariant (Copower2_1 x f a) where
  contramap f (Copower2_1 xa fab) = Copower2_1 xa (contramap1 f fab)

instance Curried Copower2_1 (Lift1 Nat) where
  curry f = Nat $ \a -> Lift $ Nat $ \b -> runNat2 f $ Copower2_1 a b
  uncurry f = nat2 $ \(Copower2_1 a b) -> runNat (lower (runNat f a)) b

class (k ~ (~>)) => Cocomplete (k :: j -> j -> *) where
  type Colim :: (i -> j) -> j

  colim :: k (f a) (Colim f)

  -- The explicit witness here allows us to quantify over all kinds i.
  -- Colim -| Const
  cocomplete :: Dict ((Colim :: (i -> j) -> j) -| Const)
  default cocomplete :: ((Colim :: (i -> j) -> j) -| Const) => Dict ((Colim :: (i -> j) -> j) -| Const)
  cocomplete = Dict

-- * @(->)@ is cocomplete

data Colim1 (f :: i -> *) where
  Colim :: f x -> Colim1 f

instance Functor Colim1 where
  fmap (Nat f) (Colim g)= Colim (f g)

instance Cosemimonoidal Colim1 where
  op2 (Colim (Lift ab)) = bimap Colim Colim ab

instance Comonoidal Colim1 where
  op0 (Colim (Const a)) = a

instance Cosemigroup m => Cosemigroup (Colim1 m) where
  comult = comultOp

instance Comonoid m => Comonoid (Colim1 m) where
  zero = zeroOp

instance Colim1 -| Const1 where
  adj = dimap (\f -> Nat $ Const . f . Colim) $ \(Nat g2cb) (Colim g) -> getConst (g2cb g)

instance Cocomplete (->) where
  type Colim = Colim1
  colim = Colim

-- * The cocompletion of @(j -> *)@ borrows its structure from @*@

data Colim2 (f :: i -> j -> *) (x :: j) where
  Colim2 :: f y x -> Colim2 f x

instance Functor Colim2 where
  fmap f = Nat $ \(Colim2 g) -> Colim2 (runNat (runNat f) g)

instance Colim2 -| Const2 where
  adj = dimap (\(Nat f) -> nat2 $ Const2 . f . Colim2) $
               \ f -> Nat $ \ xs -> case xs of
                 Colim2 fyx -> getConst2 $ runNat2 f fyx

instance Cocomplete (Nat :: (i -> *) -> (i -> *) -> *) where
  type Colim = Colim2
  colim = Nat Colim2

-- * Kan extensions

class (c ~ Hom) => HasRan (c :: k -> k -> *) | k -> c where
  type Ran :: (i -> j) -> (i -> k) -> j -> k

  ranCurried :: Dict (Curried Compose (Ran :: (i -> j) -> (i -> k) -> j -> k))
  default ranCurried :: Curried Compose (Ran :: (i -> j) -> (i -> k) -> j -> k) => Dict (Curried Compose (Ran :: (i -> j) -> (i -> k) -> j -> k))
  ranCurried = Dict

  ranProfunctor :: Category (Hom :: j -> j -> *) => Dict (Profunctor (Ran :: (i -> j) -> (i -> k) -> j -> k))
  default ranProfunctor :: Profunctor (Ran :: (i -> j) -> (i -> k) -> j -> k) => Dict (Profunctor (Ran :: (i -> j) -> (i -> k) -> j -> k))
  ranProfunctor = Dict

  -- yoneda lemma in right Kan extension form
  iotaRan :: forall (f :: i -> k) (g :: i -> k) id. (Category (Cod f), Category (Dom f), Functor g, Identity id) => Iso (Ran id f) (Ran id g) f g

  -- | return for Codensity
  jotRan  :: forall (f :: i -> k). Id ~> Ran f f

data Ran1 f g a = forall z. Functor z => Ran (Compose z f ~> g) (z a)

instance Curried Compose1 Ran1 where
  type Curryable Compose1 = Functor
  curry l = Nat (Ran l)
  uncurry l = Nat $ \ (Compose ab) -> case runNat l ab of
    Ran czfg za -> runNat czfg (Compose za)

instance HasRan (->) where
  type Ran = Ran1
  iotaRan = dimap (apply . beget rhoCompose) (curry (get rhoCompose))
  jotRan = curry (beget lambdaCompose)

instance Contravariant Ran1 where
  contramap f = nat2 $ \(Ran k z) -> Ran (k . Nat (compose . fmap (runNat f) . decompose)) z

instance Category (Hom :: j -> j -> *) => Functor (Ran1 f :: (i -> *) -> (j -> *)) where
  fmap f = Nat $ \(Ran k z) -> Ran (f . k) z

instance Functor (Ran1 f g) where
  fmap f (Ran k z) = Ran k (fmap f z)

class (c ~ Hom) => HasLan (c :: k -> k -> *) | k -> c where
  type Lan :: (i -> j) -> (i -> k) -> j -> k

  lanCocurried :: Dict (Cocurried (Lan :: (i -> j) -> (i -> k) -> j -> k) Compose)
  default lanCocurried :: Cocurried (Lan :: (i -> j) -> (i -> k) -> j -> k) Compose => Dict (Cocurried (Lan :: (i -> j) -> (i -> k) -> j -> k) Compose)
  lanCocurried = Dict

  lanProfunctor :: Category (Hom :: j -> j -> *) => Dict (Profunctor (Lan :: (i -> j) -> (i -> k) -> j -> k))
  default lanProfunctor :: Profunctor (Lan :: (i -> j) -> (i -> k) -> j -> k) => Dict (Profunctor (Lan :: (i -> j) -> (i -> k) -> j -> k))
  lanProfunctor = Dict

  -- yoneda again
  epsilonLan :: forall (f :: i -> k) (g :: i -> k) id. (Category (Cod f), Category (Dom f), Functor f, Identity id) => Iso (Lan id f) (Lan id g) f g

newtype Lan1 f g a = Lan { runLan :: forall z. Functor z => (g ~> Compose z f) ~> z a }

instance Cocurried Lan1 Compose1 where
  type Cocurryable Compose1 = Functor
  cocurry l = Nat $ \b -> Compose $ runNat l (Lan $ \f -> case runNat f b of Compose z -> z)
  uncocurry k = Nat $ \xs -> runLan xs k

instance HasLan (->) where
  type Lan = Lan1
  epsilonLan = dimap (Nat $ \l -> runLan l (beget rhoCompose))
                     (Nat $ \f -> Lan $ \k -> runNat (get rhoCompose . k) f)

instance Contravariant Lan1 where
  contramap f = nat2 $ \l -> Lan $ \k -> runLan l (Nat (compose . fmap (runNat f) . decompose) . k)

instance Category (Hom :: j -> j -> *) => Functor (Lan1 f :: (i -> *) -> (j -> *)) where
  fmap f = Nat $ \l -> Lan $ \k -> runLan l (k . f)

newtype Lan2 f g a b = Lan2 { runLan2 :: forall z. Functor z => (g ~> Compose z f) ~> z a b }

instance Cocurried Lan2 Compose2 where
  type Cocurryable Compose2 = Functor
  cocurry l = nat2 $ \b -> Compose2 $ runNat2 l (Lan2 $ \f -> case runNat2 f b of Compose2 z -> z)
  uncocurry k = nat2 $ \xs -> runLan2 xs k


instance HasLan (Nat :: (i -> *) -> (i -> *) -> *)  where
  type Lan = Lan2
  epsilonLan = dimap (nat2 $ \l -> runLan2 l (beget rhoCompose))
                     (nat2 $ \f -> Lan2 $ \k -> runNat2 (get rhoCompose . k) f)

instance Contravariant Lan2 where
  contramap f = nat3 $ \l -> Lan2 $ \k -> runLan2 l (Nat (compose . fmap (runNat f) . decompose) . k)

instance Category (Hom :: j -> j -> *) => Functor (Lan2 f :: (i -> k -> *) -> (j -> k -> *)) where
  fmap f = nat2 $ \l -> Lan2 $ \k -> runLan2 l (k . f)
