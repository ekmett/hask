{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
module Kind where

import qualified Control.Applicative as Applicative
import qualified Control.Arrow as Arrow
import Control.Category (Category(..))
import qualified Control.Comonad as Comonad
import qualified Control.Monad as Monad
import qualified Data.Constraint as Constraint
import Data.Constraint ((:-)(Sub), (\\), Dict(Dict))
import qualified Data.Functor.Contravariant as Contravariant
import qualified Data.Functor.Identity as Identity
-- import qualified Data.Monoid as Monoid
import Data.Proxy
-- import qualified Data.Semigroup as Semigroup
import Data.Tagged
import qualified Data.Traversable as Traversable
import Data.Void
import qualified Prelude
import Prelude (Either(..), ($), either, Bool, undefined)
import GHC.Exts (Constraint, Any)
import Unsafe.Coerce (unsafeCoerce)

-- * A kind-indexed family of categories

infixr 0 ~>

-- to play with enriched categories, change to (~>) :: i -> i -> j
type family (~>) :: i -> i -> *
type instance (~>) = (->)  -- @* -> * -> *@
type instance (~>) = Nat   -- @(i -> j) -> (i -> j) -> *@
type instance (~>) = (:-)  -- @Constraint -> Constraint -> *@
type instance (~>) = Unit  -- @() -> () -> *@
type instance (~>) = Empty -- @Void -> Void -> *@
type instance (~>) = Prod  -- @(i,j) -> (i, j) -> *@

-- * convenience types that make it so we can avoid explicitly talking about the kinds as much as possible
type Dom  (f :: x -> y)      = ((~>) :: x -> x -> *)
type Cod  (f :: x -> y)      = ((~>) :: y -> y -> *)
type Cod2 (f :: x -> y -> z) = ((~>) :: z -> z -> *)
type Arr  (a :: x)           = ((~>) :: x -> x -> *)

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

class Contravariant (f :: x -> y) where
  contramap :: (b ~> a) -> f a ~> f b

first :: Functor p => (a ~> b) -> p a c ~> p b c
first = runNat . fmap

lmap :: Contravariant p => (a ~> b) -> p b c ~> p a c
lmap = runNat . contramap

-- | the isomorphism that witnesses f -| u
type (f :: y -> x) -: (u :: x -> y) = forall a b a' b'. Iso (f a ~> b) (f a' ~> b') (a ~> u b) (a' ~> u b')

-- | @f -| u@ indicates f is left adjoint to u
class (Functor f, Functor u) => (f::y->x) -| (u::x->y) | f -> u, u -> f where
  adj :: f -: u

type (f :: i -> y -> x) =: (u :: i -> x -> y) = forall e e' a b a' b'. Iso (f e a ~> b) (f e' a' ~> b') (a ~> u e b) (a' ~> u e' b')

-- | @f =| u@ indicates f_e is left adjoint to u_e via an indexed adjunction
class (Functor1 f, Functor1 u) => (f::i->y->x) =| (u::i->x->y) | f -> u, u -> f where
  adj1 :: f =: u

unitAdj :: (f -| u, Category (Dom u)) => a ~> u (f a)
unitAdj = get adj id

counitAdj :: (f -| u, Category (Dom f)) => f (u b) ~> b
counitAdj = unget adj id

-- given f -| u, u is a strong monoidal functor
--
-- @
-- ap0 = get adj terminal
-- ap2 = get zipR
-- @
zipR :: (f -| u, Cartesian (Dom u), Cartesian (Cod u))
     => Iso (u a * u b) (u a' * u b') (u (a * b)) (u (a' * b'))
zipR = dimap (get adj (unget adj fst &&& unget adj snd))
             (fmap fst &&& fmap snd)

-- given f =| u, u is a strong indexed monoidal functor
zipR1 :: (f =| u, Cartesian (Cod2 u), Cartesian (Cod2 f))
     => Iso (u e a * u e b) (u e' a' * u e' b') (u e (a * b)) (u e' (a' * b'))
zipR1 = dimap (get adj1 (unget adj1 fst &&& unget adj1 snd))
              (fmap1 fst &&& fmap1 snd)

absurdL :: (f -| u, Initial z) => Iso' z (f z)
absurdL = dimap initial (unget adj initial)

absurdL1 :: (f =| u, Initial z) => Iso' z (f e z)
absurdL1 = dimap initial (unget adj1 initial)

cozipL :: (f -| u, Cocartesian (Cod u), Cocartesian (Cod f))
       => Iso (f (a + b)) (f (a' + b')) (f a + f b) (f a' + f b')
cozipL = dimap
  (unget adj (get adj inl ||| get adj inr))
  (fmap inl ||| fmap inr)

cozipL1 :: (f =| u, Cocartesian (Cod2 u), Cocartesian (Cod2 f))
       => Iso (f e (a + b)) (f e' (a' + b')) (f e a + f e b) (f e' a' + f e' b')
cozipL1 = dimap
  (unget adj1 (get adj1 inl ||| get adj1 inr))
  (fmap1 inl ||| fmap1 inr)

-- tabulated :: (f -| u) => Iso (a ^ f One) (b ^ f One) (u a) (u b)
-- splitL :: (f -| u) => Iso (f a) (f a') (a * f One) (a' * f One)

-- * common aliases
class (Functor p, Functor1 p) => Bifunctor p
instance (Functor p, Functor1 p) => Bifunctor p

class (Contravariant p, Contravariant1 p) => Bicontravariant p
instance (Contravariant p, Contravariant1 p) => Bicontravariant p

-- enriched profuncors C^op * D -> E
--
-- note: due to the fact that we use the variances in the other order, this is technically a
-- correspondence or distributor, not a profunctor
class (Contravariant p, Functor1 p) => Profunctor p
instance (Contravariant p, Functor1 p) => Profunctor p

-- Lift Prelude instances of Functor without overlap, using the kind index to say
-- these are all the instances of kind * -> *
--
-- Unfortunately that isn't true, as functors to/from k -> * that are polymorphic in k
-- overlap with these instances!
--
-- instance Prelude.Functor f => Functor f where
--   fmap = Prelude.fmap

-- instance Contravariant.Contravariant f => Contravariant f where
--    contramap = Contravariant.contramap

instance Category ((~>) :: j -> j -> *) => Functor (Nat f :: (i -> j) -> *) where
  fmap = (.)

instance Functor ((:-) f) where
  fmap = fmap1

-- We can define a functor from the category of natural transformations to Hask
newtype At (x :: i) (f :: i -> *) = At { getAt :: f x }
_At = dimap getAt At

instance Functor (At x) where
  fmap (Nat f) = _At f

instance Semimonoidal (At x) where
  ap2 (At fx, At fy) = At (Lift (fx, fy))

instance Monoidal (At x) where
  ap0 = At . Const

instance Semigroup m => Semigroup (At x m) where
  mult = multM

instance Monoid m => Monoid (At x m) where
  one = oneM

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

class b => ConstC b a
instance b => ConstC b a

instance Constant ConstC where
  type Const = ConstC
  _Const = dimap (Sub Dict) (Sub Dict)

instance Functor ConstC where
  fmap f = Nat (_Const f)

instance Functor (ConstC b) where
  fmap _ = Sub Dict

-- * Ends

type family End :: (i -> i -> j) -> j

newtype End1 f = End { getEnd :: forall x. f x x }
type instance End = End1

instance Functor End1 where
  fmap f (End fcc) = End $ runNat2 f fcc

newtype End2 f y = End2 { getEnd2 :: forall x. f x x y }
type instance End = End2

instance Functor End2 where
  fmap f = Nat $ \(End2 fcc) -> End2 $ runNat3 f fcc

newtype End3 f y z = End3 { getEnd3 :: forall x. f x x y z }
type instance End = End3

instance Functor End3 where
  fmap f = nat2 $ \(End3 fcc) -> End3 $ runNat4 f fcc

-- assumes p is contravariant in its first argument, covariant in its second
class EndC (p :: i -> i -> Constraint) where
  endDict :: Dict (p a a)

type instance End = EndC

instance p Any Any => EndC (p :: i -> i -> Constraint) where
  endDict = case unsafeCoerce (id :: p Any Any :- p Any Any) :: p Any Any :- p a a of
    Sub d -> d

instance Functor EndC where
  fmap f = dimap (Sub endDict) (Sub Dict) (runAny f) where
    runAny :: (p ~> q) -> p Any Any ~> q Any Any
    runAny = runNat2

-- * Coends

type family Coend :: (i -> i -> j) -> j

data Coend1 f where
  Coend :: f x x -> Coend1 f

type instance Coend = Coend1

instance Functor Coend1 where
  fmap f (Coend fcc) = Coend $ runNat2 f fcc

data Coend2 f y where
  Coend2 :: f x x y -> Coend2 f y

type instance Coend = Coend2

instance Functor Coend2 where
  fmap f = Nat $ \(Coend2 fcc) -> Coend2 $ runNat3 f fcc

-- * -^J -| Limit

type family Limit :: (i -> j) -> j

newtype Limit1 (f :: i -> *) = Limit { getLimit :: forall x. f x }
type instance Limit = Limit1

instance Functor Limit1 where
  fmap (Nat f) (Limit g) = Limit (f g)

instance Semimonoidal Limit1 where
  ap2 (Limit f, Limit g) = Limit (Lift (f, g))

instance Monoidal Limit1 where
  ap0 () = Limit $ Const ()

instance Semigroup m => Semigroup (Limit1 m) where
  mult = multM

instance Monoid m => Monoid (Limit1 m) where
  one = oneM

instance Const1 -| Limit1 where
  adj = dimap (\f a -> Limit (runNat f (Const a))) $ \h -> Nat $ getLimit . h . getConst

newtype Limit2 (f :: i -> j -> *) (y :: j) = Limit2 { getLimit2 :: forall x. f x y }
type instance Limit = Limit2

instance Functor Limit2 where
  fmap f = Nat $ \(Limit2 g) -> Limit2 (runNat (runNat f) g)

-- instance Monoidal Limit2 -- instantiate when Nat on 2 arguments is made Cartesian

instance Const2 -| Limit2 where
  adj = dimap (\(Nat f) -> Nat $ \ a -> Limit2 (runNat f (Const2 a))) $ \(Nat h) -> nat2 $ getLimit2 . h . getConst2

-- has to abuse Any because any inhabits every kind, but it is not a good choice of Skolem!
class LimitC (p :: i -> Constraint) where
  limitDict :: Dict (p a)

instance p Any => LimitC (p :: i -> Constraint) where
  limitDict = case unsafeCoerce (id :: p Any :- p Any) :: p Any :- p a of
    Sub d -> d

type instance Limit = LimitC

instance Functor LimitC where
  fmap f = dimap (Sub limitDict) (Sub Dict) (runAny f) where
    runAny :: (p ~> q) -> p Any ~> q Any
    runAny = runNat

instance Semimonoidal LimitC where
  ap2 = get zipR

instance Monoidal LimitC where
  ap0 = Sub Dict

-- instance Semigroup m => Semigroup (LimitC m) where mult = multM

instance Monoid m => Monoid (LimitC m) where
  one = oneM

instance ConstC -| LimitC where
  adj = dimap (hither . runNat) (\b -> Nat $ dimap (Sub Dict) (Sub limitDict) b) where
    hither :: (ConstC a Any :- f Any) -> a :- LimitC f
    hither = dimap (Sub Dict) (Sub Dict)

-- * Colimit -| -^J

type family Colimit :: (i -> j) -> j
type instance Colimit = Colimit1
type instance Colimit = Colimit2

data Colimit1 (f :: i -> *) where
  Colimit :: f x -> Colimit1 f

instance Functor Colimit1 where
  fmap (Nat f) (Colimit g)= Colimit (f g)

instance Cosemimonoidal Colimit1 where
  op2 (Colimit (Lift ab)) = bimap Colimit Colimit ab

instance Comonoidal Colimit1 where
  op0 (Colimit (Const a)) = a

instance Cosemigroup m => Cosemigroup (Colimit1 m) where
  comult = comultOp

instance Comonoid m => Comonoid (Colimit1 m) where
  zero = zeroOp

instance Colimit1 -| Const1 where
  adj = dimap (\f -> Nat $ Const . f . Colimit) $ \(Nat g2cb) (Colimit g) -> getConst (g2cb g)

data Colimit2 (f :: i -> j -> *) (x :: j) where
  Colimit2 :: f y x -> Colimit2 f x

instance Functor Colimit2 where
  fmap f = Nat $ \(Colimit2 g) -> Colimit2 (runNat (runNat f) g)

-- instance Comonoidal Colimit2
-- instance Comonoid m => Comonoid (Colimit1 m)

instance Colimit2 -| Const2 where
  adj = dimap (\(Nat f) -> nat2 $ Const2 . f . Colimit2) $
               \ f -> Nat $ \ xs -> case xs of
                 Colimit2 fyx -> getConst2 $ runNat2 f fyx

-- * Support for Tagged and Proxy

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

instance Contravariant1 p => Contravariant (Lift1 p f) where
  contramap (Nat f) = Nat $ _Lift (contramap1 f)

instance Functor1 p => Functor (Lift1 p f) where
  fmap (Nat f) = Nat (_Lift $ fmap1 f)

instance (Functor p, Functor1 p, Functor f, Functor g) => Functor (Lift1 p f g) where
  fmap f = _Lift (bimap (fmap f) (fmap f))

-- ** LiftC

class r (p a) (q a) => LiftC r p q a
instance r (p a) (q a) => LiftC r p q a

instance Functor p => Functor (LiftC p) where
  fmap f = nat2 $ _Lift $ first $ runNat f

instance Contravariant p => Contravariant (LiftC p) where
  contramap f = nat2 $ _Lift $ lmap $ runNat f

instance Functor1 p => Functor (LiftC p e) where
  fmap (Nat f) = Nat (_Lift $ fmap1 f)

instance Contravariant1 p => Contravariant (LiftC p e) where
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

instance Functor1 p => Functor (Lift2 p f) where
  fmap (Nat f) = Nat (_Lift $ fmap1 f)

instance Contravariant1 p => Contravariant (Lift2 p f) where
  contramap = contramap1

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
  contramap f = Nat $ dimap Hom runHom (lmap f)

-- * Misc

instance Functor Tagged where
  fmap _ = Nat (_Tagged id)

instance Functor (Either e) where
  fmap = Arrow.right

instance Functor (Tagged e) where
  fmap = Prelude.fmap

data Via (a :: x) (b :: x) (s :: x) (t :: x) where
  Via :: (s ~> a) -> (b ~> t) -> Via a b s t

instance Functor1 ((~>) :: x -> x -> *) => Functor (Via :: x -> x -> x -> x -> *) where
  fmap f = nat3 $ \(Via sa bt) -> Via (fmap1 f sa) bt

instance Contravariant1 ((~>) :: x -> x -> *) => Contravariant (Via :: x -> x -> x -> x -> *) where
  contramap f = nat3 $ \(Via sa bt) -> Via (contramap1 f sa) bt

instance Functor ((~>) :: x -> x -> *) => Functor (Via a :: x -> x -> x -> *) where
  fmap f = nat2 $ \(Via sa bt) -> Via sa (first f bt)

instance Contravariant ((~>) :: x -> x -> *) => Contravariant (Via a :: x -> x -> x -> *) where
  contramap f = nat2 $ \(Via sa bt) -> Via sa (lmap f bt)

instance Functor ((~>) :: x -> x -> *) => Functor (Via a b :: x -> x -> *) where
  fmap f = Nat $ \(Via sa bt) -> Via (first f sa) bt

instance Contravariant ((~>) :: x -> x -> *) => Contravariant (Via a b :: x -> x -> *) where
  contramap f = Nat $ \(Via sa bt) -> Via (lmap f sa) bt

instance Functor1 ((~>) :: x -> x -> *) => Functor (Via a b s :: x -> *) where
  fmap f (Via sa bt) = Via sa (fmap1 f bt)

instance Contravariant1 ((~>) :: x -> x -> *) => Contravariant (Via a b s :: x -> *) where
  contramap f (Via sa bt) = Via sa (contramap1 f bt)

-- |
-- @
-- get   = via _Get
-- unget = via _Unget
-- un    = via _Un
-- @
via :: forall (a :: *) (b :: *) (r :: *) (p :: x -> x -> *) (c :: x) (t :: *) (u :: *).
     Category p => (Via a b a b -> Via r (p c c) u t) -> (t -> u) -> r
via l m = case l (Via id id) of
  Via csa dbt -> csa $ m (dbt id)

mapping :: (Functor f, Functor f', Category (Dom f)) => (Via a b a b -> Via a b s t) -> Iso (f s) (f' t) (f a) (f' b)
mapping l = case l (Via id id) of
  Via csa dbt -> dimap (fmap csa) (fmap dbt)

lmapping :: (Contravariant f, Contravariant f', Category (Dom f)) => (Via s t s t -> Via s t a b) -> Iso (f s x) (f' t y) (f a x) (f' b y)
lmapping l = case l (Via id id) of
  Via csa dbt -> dimap (lmap csa) (lmap dbt)

swapping :: (Profunctor f, Profunctor f', Category (Dom f), Category (Cod2 f), Category (Cod2 f'))
         => (Via a b a b -> Via a b s t) -> Iso (f a s) (f' b t) (f s a) (f' t b)
swapping l = case l (Via id id) of
  Via csa dbt -> dimap (dimap csa csa) (dimap dbt dbt)

newtype Hom a b = Hom { runHom :: a ~> b }
_Hom = dimap runHom Hom

instance Category ((~>) :: x -> x -> *) => Contravariant (Hom :: x -> x -> *) where
  contramap f = Nat (_Hom (.f))

instance Category ((~>) :: x -> x -> *) => Functor (Hom e :: x -> *) where
  fmap g (Hom h) = Hom (g . h)

instance Contravariant (->) where
  contramap f = Nat (. f)

instance Contravariant ((~>)::j->j-> *) => Contravariant (Nat::(i->j)->(i->j)-> *) where
  contramap (Nat f) = Nat $ \g -> Nat $ lmap f $ runNat g

instance Contravariant Tagged where
  contramap _ = Nat (_Tagged id)

instance Contravariant (Const1 k) where
  contramap _ = _Const id

instance Contravariant (Const2 k) where
  contramap _ = _Const id

type Ungetter t b = forall p. (Choice p, Functor p) => p b b -> p t t

unto :: (b ~> t) -> Ungetter t b
unto f = bimap f f

type Iso s t a b = forall p. Profunctor p => p a b -> p s t
type Iso' s a = Iso s s a a

bicontramap :: (Bicontravariant p, Category (Cod2 p)) => (a ~> b) -> (c ~> d) -> p b d ~> p a c
bicontramap f g = lmap f . contramap1 g

type Getter s a = forall p. (Strong p, Contravariant1 p) => p a a -> p s s

to :: (s ~> a) -> Getter s a
to f = bicontramap f f

newtype Get r a b = Get { runGet :: a ~> r }
_Get = dimap runGet Get

instance Category (Arr r) => Contravariant (Get r) where
  contramap f = Nat (_Get (. f))

instance Contravariant (Get r a) where
  contramap _ = _Get id

instance Functor (Get r a) where
  fmap _ = _Get id

get :: (Category c, c ~ (~>)) => (Get a a a -> Get a s s) -> c s a
get l = runGet $ l (Get id)
-- get = via _Get

-- * Unget

newtype Unget r a b = Unget { runUnget :: r ~> b }
_Unget = dimap runUnget Unget

instance Functor (Unget r) where
  fmap _ = Nat $ _Unget id

instance Contravariant (Unget r) where
  contramap _ = Nat $ _Unget id

instance Category ((~>) :: i -> i -> *) => Functor (Unget (r :: i) (a :: k)) where
  fmap f = _Unget (f .)

unget :: (Category c, c ~ (~>)) => (Unget b b b -> Unget b t t) -> c b t
unget l = runUnget $ l (Unget id)
-- unget = via _Unget

(#) :: (Unget b b b -> Unget b t t) -> b -> t
(#) = unget

-- * Un

-- signatures needed to require endoprofunctors
newtype Un (p::i->i->j) (a::i) (b::i) (s::i) (t::i) = Un { runUn :: p t s ~> p b a }
_Un = dimap runUn Un

instance (Category ((~>)::j->j-> *), Functor1 p) => Contravariant (Un (p::i->i->j) a b) where
  contramap f = Nat $ _Un $ dimap Hom runHom $ lmap (fmap1 f)

instance (Category ((~>)::j->j-> *), Contravariant1 p) => Functor (Un (p::i->i->j) a b) where
  fmap f = Nat $ _Un $ dimap Hom runHom $ lmap (contramap1 f)

instance (Category ((~>)::j->j-> *), Contravariant p) => Functor (Un (p::i->i->j) a b s) where
  fmap g = _Un $ dimap Hom runHom $ lmap (lmap g)

instance (Category ((~>)::j->j-> *), Functor p) => Contravariant (Un (p::i->i->j) a b s) where
  contramap f = _Un $ dimap Hom runHom $ lmap (first f)

un :: (Un p a b a b -> Un p a b s t) -> p t s -> p b a
un l = runUn $ l (Un id)
-- un = via _Un

class (Contravariant p, Functor p) => Phantom p
instance (Contravariant p, Functor p) => Phantom p

bimap :: (Bifunctor p, Category (Cod2 p)) => (a ~> b) -> (c ~> d) -> p a c ~> p b d
bimap f g = first f . fmap1 g

dimap :: (Profunctor p, Category (Cod2 p)) => (a ~> b) -> (c ~> d) -> p b c ~> p a d
dimap f g = lmap f . fmap1 g

class (Bifunctor p, Profunctor (Cod2 p), Category (Cod2 p)) => Pretensor p where
  associate :: Iso (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))

instance Pretensor (,) where
  associate   = dimap (\((a,b),c) -> (a,(b,c)))
                      (\(a,(b,c)) -> ((a,b),c))

instance Pretensor Either where
  associate = dimap hither yon where
    hither (Left (Left a)) = Left a
    hither (Left (Right b)) = Right (Left b)
    hither (Right c) = Right (Right c)
    yon (Left a) = Left (Left a)
    yon (Right (Left b)) = Left (Right b)
    yon (Right (Right c)) = Right c

instance Pretensor (&) where
  associate   = dimap (Sub Dict) (Sub Dict)

instance Category ((~>) :: i -> i -> *) => Pretensor (Prof :: (i -> i -> *) -> (i -> i -> *) -> i -> i -> *) where
  associate = associateProf

-- tensor for a monoidal category
class Pretensor p => Tensor (p :: x -> x -> x) where
  type I p :: x
  lambda    :: Iso (p (I p) a) (p (I p) a') a a'
  rho       :: Iso (p a (I p)) (p a' (I p)) a a'

instance Tensor (,) where
  type I (,) = ()
  lambda = dimap (\((), a) -> a) ((,) ())
  rho    = dimap (\(a, ()) -> a) (\a -> (a, ()))

instance Tensor Either where
  type I Either = Void
  lambda = dimap (\(Right a) -> a) Right
  rho = dimap (\(Left a) -> a) Left

instance Tensor (&) where
  type I (&) = (() :: Constraint)
  lambda      = dimap (Sub Dict) (Sub Dict)
  rho         = dimap (Sub Dict) (Sub Dict)

associateLift :: (Lifted s, Pretensor p)
  => Iso (s p (s p f g) h) (s p (s p f' g') h')
         (s p f (s p g h)) (s p f' (s p g' h'))
associateLift = dimap
  (Nat $ _Lift $ fmap1 (unget _Lift) . get associate . first (get _Lift))
  (Nat $ _Lift $ first (unget _Lift) . unget associate . fmap1 (get _Lift))

lambdaLift :: (Constant k, Lifted s, Tensor p) =>
   Iso (s p (k (I p)) f) (s p (k (I p)) g) f g
lambdaLift   = dimap
   (Nat $ lmap (first (get _Const) . get _Lift) (get lambda))
   (Nat $ fmap1 (unget _Lift . first (unget _Const)) (unget lambda))

rhoLift :: (Constant k, Lifted s, Tensor p) =>
   Iso (s p f (k (I p))) (s p g (k (I p))) f g
rhoLift =
  dimap (Nat $ lmap (fmap1 (get _Const) . get _Lift) (get rho))
        (Nat $ fmap1 (unget _Lift . fmap1 (unget _Const)) (unget rho))

instance Pretensor p => Pretensor (Lift1 p) where
  associate   = associateLift

instance Tensor p => Tensor (Lift1 p) where
  type I (Lift1 p) = Const1 (I p)
  lambda      = lambdaLift
  rho         = rhoLift

instance Pretensor p => Pretensor (Lift2 p) where
  associate   = associateLift

instance Tensor p => Tensor (Lift2 p) where
  type I (Lift2 p) = Const2 (I p)
  lambda      = lambdaLift
  rho         = rhoLift

instance Pretensor p => Pretensor (LiftC p) where
  associate   = associateLift

instance Tensor p => Tensor (LiftC p) where
  type I (LiftC p) = ConstC (I p)
  lambda      = lambdaLift
  rho         = rhoLift

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

-- forward profunctor composition forms a weak category.
data Prof :: (i -> j -> *) -> (j -> k -> *) -> i -> k -> * where
  Prof :: p a b -> q b c -> Prof p q a c

instance Functor Prof where
  fmap f = nat3 $ \(Prof p q) -> Prof (runNat2 f p) q

instance Functor (Prof p) where
  fmap f = nat2 $ \(Prof p q) -> Prof p (runNat2 f q)

instance Contravariant p => Contravariant (Prof p q) where
  contramap f = Nat $ \(Prof p q) -> Prof (runNat (contramap f) p) q

instance Functor1 q => Functor (Prof p q a) where
  fmap f (Prof p q) = Prof p (fmap1 f q)

associateProf :: Iso (Prof (Prof p q) r) (Prof (Prof p' q') r')
                     (Prof p (Prof q r)) (Prof p' (Prof q' r'))
associateProf = dimap
  (nat2 $ \ (Prof (Prof a b) c) -> Prof a (Prof b c))
  (nat2 $ \ (Prof a (Prof b c)) -> Prof (Prof a b) c)

{-
lambdaProf :: (Contravariant p, Category q, q ~> (~>) => Prof q p ~> p
lambdaProf = nat2 $ \(Prof h p) -> lmap h p

rhoProf :: (Category q, q ~ (~>)) => p ~> Prof p q
rhoProf = nat2 $ \p -> Prof p id
-}

newtype ProfR p q a b = ProfR { runProfR :: forall x. p x a -> q x b }

-- ProfL? =| Prof =| ProfR

instance Contravariant ProfR where
  contramap f = nat3 $ \(ProfR pq) -> ProfR $ \p -> pq (runNat2 f p)

instance Functor (ProfR p) where
  fmap f = nat2 $ \(ProfR pq) -> ProfR $ \p -> runNat2 f (pq p)

instance Functor1 p => Contravariant (ProfR p q) where
  contramap f = Nat $ \(ProfR pq) -> ProfR $ \p -> pq (fmap1 f p)

instance Functor1 q => Functor (ProfR p q a) where
  fmap f (ProfR pq) = ProfR $ \p -> fmap1 f (pq p)

instance Contravariant1 p => Functor (ProfR p q) where
  fmap f = Nat $ \(ProfR pq) -> ProfR $ \p -> pq (contramap1 f p)

instance Contravariant1 q => Contravariant (ProfR p q a) where
  contramap f (ProfR pq) = ProfR $ \p -> contramap1 f (pq p)

instance Prof =| ProfR where
-- adj1 :: Iso (Prof p q ~> r) (Prof p' q' ~> r') (q ~> ProfR p r) (q' ~> ProfR p' r')
  adj1 = dimap (\k -> nat2 $ \p -> ProfR $ \q -> runNat2 k (Prof q p))
               (\k -> nat2 $ \(Prof p q) -> runProfR (runNat2 k q) p) -- runR (runNat (runNat k) p) q)

instance Prof e -| ProfR e where
  adj = adj1

-- Terminal objects

class One ~ t => Terminal (t :: i) | i -> t where
  type One :: i
  terminal :: a ~> t

instance Terminal () where
  type One = ()
  terminal _ = ()

-- we can only offer the terminal object for Nat :: (i -> *), not Nat :: (i -> j)
instance Terminal t => Terminal (Const1 t) where
  type One = Const1 One
  terminal = Nat (unget _Const . terminal)

instance Terminal t => Terminal (Const2 t) where
  type One = Const2 One
  terminal = Nat (unget _Const . terminal)

instance Terminal (() :: Constraint) where
  type One = (() :: Constraint)
  terminal = Constraint.top

instance Terminal (ConstC ()) where
  type One = ConstC ()
  terminal = Nat (unget _Const . terminal)

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
class (h ~ (~>), Symmetric ((*)::i->i->i), Pretensor ((*)::i->i->i)) => Precartesian (h :: i -> i -> *) | i -> h where
  type (*) :: i -> i -> i
  fst   :: forall (a::i) (b::i). a * b ~> a
  snd   :: forall (a::i) (b::i). a * b ~> b
  (&&&) :: forall (a::i) (b::i) (c::i). (a ~> b) -> (a ~> c) -> a ~> b * c

class    (h ~ (~>), Tensor ((*)::i->i->i), Terminal (I ((*)::i->i->i)), Precartesian h) => Cartesian (h ::i->i-> *) | i -> h
instance (h ~ (~>), Tensor ((*)::i->i->i), Terminal (I ((*)::i->i->i)), Precartesian h) => Cartesian (h ::i->i-> *)

instance Precartesian (->) where
  type (*) = (,)
  fst   = Prelude.fst
  snd   = Prelude.snd
  (&&&) = (Arrow.&&&)

instance Precartesian (:-) where
  type (*) = (&)
  fst = Sub Dict
  snd = Sub Dict
  p &&& q = Sub $ Dict \\ p \\ q

instance Precartesian (Nat :: (i -> *) -> (i -> *) -> *) where
  type (*) = Lift (,)
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ Lift . (f &&& g)

instance Precartesian (Nat :: (i -> j -> *) -> (i -> j -> *) -> *) where
  type (*) = Lift2 (*)
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ unget _Lift . (f &&& g)

instance Precartesian (Nat :: (i -> Constraint) -> (i -> Constraint) -> *) where
  type (*) = LiftC (&)
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ unget _Lift . (f &&& g)

-- todo make this a pre-req to Tensor?
class (Precartesian ((~>) :: i -> i -> *), Profunctor p) => Strong (p :: i -> i -> *) where
  {-# MINIMAL _1 | _2 #-}
  _1 :: p a b -> p (a * c) (b * c)
  _1 = dimap swap swap . _2
  _2 :: p a b -> p (c * a) (c * b)
  _2 = dimap swap swap . _1

instance Strong (->) where
  _1 = first
  _2 = fmap1

instance Strong (:-) where
  _1 = first
  _2 = fmap1

instance Strong (Nat::(i-> *)->(i-> *)-> *) where
  _1 = first
  _2 = fmap1

instance Strong (Nat::(i-> Constraint)->(i-> Constraint)-> *) where
  _1 = first
  _2 = fmap1

instance Precartesian ((~>)::i->i-> *) => Strong (Get (r::i)) where
  _1 = _Get (. fst)

type Lens s t a b = forall p. Strong p => p a b -> p s t

infixl 6 +
class (h ~ (~>), Symmetric ((+)::i->i->i), Pretensor ((+)::i->i->i)) => Precocartesian (h :: i -> i -> *) | i -> h where
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
  inl = Nat (unget _Lift . inl)
  inr = Nat (unget _Lift . inr)
  Nat f ||| Nat g = Nat $ (f ||| g) . get _Lift

instance Precocartesian (Nat :: (i -> j -> *) -> (i -> j -> *) -> *) where
  type (+) = Lift2 (+)
  inl = Nat (unget _Lift . inl)
  inr = Nat (unget _Lift . inr)
  Nat f ||| Nat g = Nat $ (f ||| g) . get _Lift

class (Precocartesian ((~>) :: i -> i -> *), Profunctor p) => Choice (p :: i -> i -> *) where
  {-# MINIMAL _Left | _Right #-}
  _Left  :: p a b -> p (a + c) (b + c)
  _Left = dimap swap swap . _Right
  _Right :: p a b -> p (c + a) (c + b)
  _Right = dimap swap swap . _Left

instance Choice (->) where
  _Left = Arrow.left
  _Right = Arrow.right

instance Choice (Nat :: (i -> *) -> (i -> *) -> *) where
  _Left (Nat f) = Nat $ _Lift (_Left f)
  _Right (Nat g) = Nat $ _Lift (_Right g)

instance Choice (Nat :: (i -> j -> *) -> (i -> j -> *) -> *) where
  _Left (Nat f) = Nat $ _Lift (_Left f)
  _Right (Nat g) = Nat $ _Lift (_Right g)

instance Choice Tagged where
  _Left  = bimap inl inl
  _Right = bimap inr inr

instance Precocartesian ((~>) :: i -> i -> *) => Choice (Unget (r :: i)) where
  _Left = bimap inl inl
  _Right = bimap inr inr

type Prism s t a b = forall p. Choice p => p a b -> p s t

-- * Factoring

factor :: (Functor1 (f :: j -> i -> i), Precocartesian (Cod2 f)) => f e b + f e c ~> f e (b + c)
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


-- * CCCs

type a ^ b = Exp b a
infixr 8 ^

class (Cartesian k, (*) =| (Exp :: x -> x -> x), Profunctor (Exp :: x -> x -> x)) => CCC (k :: x -> x -> *) | x -> k where
  type Exp :: x -> x -> x
  curried :: forall (a :: x) (b :: x) (c :: x) (a' :: x) (b' :: x) (c' :: x). Iso (a * b ~> c) (a' * b' ~> c') (a ~> c^b) (a' ~> c'^b')

instance CCC (->) where
  type Exp = (->)
  curried = dimap Prelude.curry Prelude.uncurry

instance CCC (Nat :: (i -> *) -> (i -> *) -> *) where
  type Exp = Lift (->)
  curried = dimap hither yon where
    hither (Nat f) = Nat $ \a -> Lift $ \b -> f (Lift (a, b))
    yon (Nat f) = Nat $ \(Lift (a,b)) -> lower (f a) b

curry :: forall (a :: i) (b :: i) (c :: i). CCC ((~>)::i -> i -> *) => ((a * b) ~> c) -> a ~> c^b
curry = get curried

uncurry :: forall (a :: i) (b :: i) (c :: i). CCC ((~>)::i -> i -> *) => (a ~> c^b) -> (a * b) ~> c
uncurry = unget curried

apply :: forall (a :: i) (b :: i). CCC ((~>)::i -> i -> *) => b^a * a ~> b
apply = uncurry id

unapply :: forall (a :: i) (b :: i). CCC ((~>) :: i -> i -> *) => a ~> (a * b)^b
unapply = curry id

ccc :: CCC ((~>) :: i -> i -> *) => (*) =: (Exp :: i -> i -> i)
ccc = dimap (. swap) (. swap) . curried

instance (,) =| (->) where
  adj1 = ccc

instance (,) e -| (->) e where
  adj = ccc

instance Lift1 (,) =| Lift1 (->) where
  adj1 = ccc

instance Lift1 (,) e -| Lift1 (->) e where
  adj = ccc

-- semimonoidal functors preserve the structure of our pretensor and take semimonoid objects to semimonoid objects
class (Precartesian ((~>) :: x -> x -> *), Precartesian ((~>) :: y -> y -> *), Functor f) => Semimonoidal (f :: x -> y) where
  ap2 :: f a * f b ~> f (a * b)

-- monoidal functors preserve the structure of our tensor and take monoid objects to monoid objects
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
-- instance Applicative.Applicative f => Monoidal f where
--   ap0 = Applicative.pure
--   ap2 = uncurry $ Applicative.liftA2 (,)

ap2Applicative :: Applicative.Applicative f => f a * f b -> f (a * b)
ap2Applicative = uncurry $ Applicative.liftA2 (,)

instance Semimonoidal ((:-) f) where
  ap2 = uncurry (&&&)

instance Monoidal ((:-) f) where
  ap0 () = terminal

instance Semigroup (f :- m) where -- every m is a semimonoid
  mult = multM

instance Monoid m => Monoid (f :- m) where
  one = oneM

instance Semimonoidal (Lift1 (->) f) where
  ap2 = get zipR

instance Monoidal (Lift1 (->) f) where
  ap0 = curry fst

instance Semigroup m => Semigroup (Lift1 (->) f m) where
  mult = multM

instance Monoid m => Monoid (Lift1 (->) f m) where
  one = oneM

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
  join :: m (m a) ~> m a

-- todo: prove join must respect this?
class (Monoidal m, Semimonad m) => Monad m
instance (Monoidal m, Semimonad m) => Monad m

-- instance (Semimonoidal m, Prelude.Monad m) => Semimonad m where
-- instance (Monoidal m, Prelude.Monad m) => Monad m where
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

instance Cosemimonoidal Identity.Identity where
  op2 = bimap Identity.Identity Identity.Identity . Identity.runIdentity

instance Comonoidal Identity.Identity where
  op0 = Identity.runIdentity

instance Cosemigroup m => Cosemigroup (Identity.Identity m) where
  comult = comultOp

instance Comonoid m => Comonoid (Identity.Identity m) where
  zero = zeroOp

instance Cosemimonoidal (At x) where
  op2 (At (Lift eab))= bimap At At eab

instance Comonoidal (At x) where
  op0 (At (Const x)) = x

instance Cosemigroup m => Cosemigroup (At x m) where
  comult = comultOp

instance Comonoid m => Comonoid (At x m) where
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

instance Identity Identity.Identity where
  type Id = Identity.Identity
  _Id = dimap Identity.runIdentity Identity.Identity

instance Functor Identity.Identity where
  fmap = Prelude.fmap

instance Identity.Identity -| Identity.Identity where
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

-- a monoid object in a cartesian category
class Cartesian ((~>) :: i -> i -> *) => Monoid (m :: i) where
  one  :: One ~> m

class Precartesian ((~>) :: i -> i -> *) => Semigroup (m :: i) where
  mult :: m * m ~> m

-- monoidal functors take monoids to monoids

oneM :: (Monoidal u, Monoid m) => One ~> u m
oneM = fmap one . ap0

multM :: (Semimonoidal u, Semigroup m) => u m * u m ~> u m
multM = fmap mult . ap2

-- instance Semigroup.Semigroup m => Semigroup m where
--   mult = uncurry Monoid.mappend

-- instance (Semigroup.Semigroup m, Monoid.Monoid m) => Monoid m where
--   one () = Monoid.mempty

instance Semigroup (Const1 ()) where
  mult = get lambda

instance Monoid (Const1 ()) where
  one = id

instance Semigroup (p :: Constraint) where
  mult = Sub Dict

instance Monoid (() :: Constraint) where
  one = id

mappend :: (Semigroup m, CCC (Arr m)) => m ~> m^m
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
  strength :: a * f b ~> f (a * b)

-- instance (Functor f, Prelude.Functor f) => Strength f where
instance Functor f => Strength (f :: * -> *) where
  strength (a,fb) = fmap ((,) a) fb

-- proposition: all right adjoints on Cartesian categories should be strong
-- strengthR   :: (f -| u, Cartesian (Dom u)) => a * u b ~> u (a * b)
-- costrengthL :: (f -| u, Cartesian (Dom f)) => f (a + b) ~> a + f b

-- what is usually called 'costrength' is more like a 'left strength' or a 'right strength'
-- repurposing this term for a real 'co'-strength
class Functor f => Costrength (f :: x -> x) where
  costrength :: f (a + b) ~> a + f b

instance (Functor f, Traversable.Traversable f) => Costrength f where
  costrength = Traversable.sequence

ap :: (Semimonoidal f, CCC (Dom f), CCC (Cod f)) => f (b ^ a) ~> f b ^ f a
ap = curry (fmap apply . ap2)

return :: (Monoidal f, Strength f, CCC (Dom f)) => a ~> f a
return = fmap (get lambda . swap) . strength . fmap1 ap0 . unget rho

class (Functor f, Category (Dom f)) => Cosemimonad f where
  {-# MINIMAL (duplicate | extend) #-}
  duplicate :: f a ~> f (f a)
  default duplicate :: Category (Dom f) => f a ~> f (f a)
  duplicate = extend id

  extend :: (f a ~> b) -> f a ~> f b
  extend f = fmap f . duplicate

class Cosemimonad f => Comonad f where
  extract :: f a ~> a

-- indexed store
data Store1 s a i = Store1 (s ~> a) (s i)

instance Functor (Store1 s) where
  fmap f = Nat $ \(Store1 g s) -> Store1 (f . g) s

instance Cosemimonad (Store1 s) where
  duplicate = Nat $ \(Store1 f s) -> Store1 (Nat $ Store1 f) s

instance Comonad (Store1 s) where
  extract = Nat $ \(Store1 f s) -> runNat f s

-- The dual of Conor McBride's "Atkey" adapted to this formalism
--
-- Cokey i :: Hask -> Nat
-- Cokey :: x -> * -> x -> *
newtype Cokey i a j = Cokey { runCokey :: (i ~ j) => a }

instance Functor (Cokey i) where
  fmap f = Nat $ \xs -> Cokey $ f (runCokey xs)

instance Semimonoidal (Cokey i) where
  ap2 = Nat $ \ab -> Cokey $ case ab of
    Lift (Cokey a, Cokey b) -> (a, b)

instance Monoidal (Cokey i) where
  ap0 = Nat $ \a -> Cokey (getConst a)

instance Semigroup m => Semigroup (Cokey i m) where
  mult = multM

instance Monoid m => Monoid (Cokey i m) where
  one = oneM

-- Conor McBride's "Atkey" adapted to this formalism
--
-- Key i :: Hask -> Nat
-- Key :: x -> * -> x -> *
data Key i a j where
  Key :: a -> Key i a i

instance Functor (Key i) where
  fmap f = Nat $ \ (Key a) -> Key (f a)

instance Cosemimonoidal (Key i) where
  op2 = Nat $ \(Key eab) -> Lift (bimap Key Key eab)

instance Comonoidal (Key i) where
  op0 = Nat $ \(Key v) -> Const v

instance Cosemigroup m => Cosemigroup (Key i m) where
  comult = comultOp

instance Comonoid m => Comonoid (Key i m) where
  zero = zeroOp

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

-- | Copower e -| (~>) e
--
-- note this is forced to be on the 'wrong side' like products in Haskell.
type family Copower :: x -> * -> x

type instance Copower = (,)
type instance Copower = Copower1
type instance Copower = Copower2

-- Nat :: (i -> *) -> (i -> *) -> * is tensored. (Copowered over Hask)
data Copower1 f x a = Copower (f a) x

instance Functor Copower1 where
  fmap (Nat f) = nat2 $ \(Copower fa x) -> Copower (f fa) x

instance Functor (Copower1 f) where
  fmap f = Nat $ \(Copower fa x) -> Copower fa (f x)

instance Functor f => Functor  (Copower1 f a) where
  fmap f (Copower fa x) = Copower (fmap f fa) x

instance Contravariant f => Contravariant (Copower1 f a) where
  contramap f (Copower fa x) = Copower (contramap f fa) x

instance Copower1 =| Nat where
  adj1 = dimap (\(Nat f) a -> Nat $ \e -> f (Copower e a))
              (\f -> Nat $ \(Copower e a) -> runNat (f a) e)

instance Copower1 e -| Nat e where
  adj = adj1

-- Nat :: (i -> j -> *) -> (i -> j -> *) -> * is tensored. (Copowered over Hask)
data Copower2 f x a b = Copower2 (f a b) x

instance Functor Copower2 where
  fmap f = nat3 $ \(Copower2 fab x) -> Copower2 (runNat2 f fab) x

instance Functor (Copower2 f) where
  fmap f = nat2 $ \(Copower2 fab x) -> Copower2 fab (f x)

instance Functor f => Functor (Copower2 f x) where
  fmap f = Nat $ \(Copower2 fa x) -> Copower2 (first f fa) x

instance Contravariant f => Contravariant (Copower2 f x) where
  contramap f = Nat $ \(Copower2 fa x) -> Copower2 (lmap f fa) x

instance Functor1 f => Functor (Copower2 f x a) where
  fmap f (Copower2 fab x) = Copower2 (fmap1 f fab) x

instance Contravariant1 f => Contravariant (Copower2 f x a) where
  contramap f (Copower2 fab x) = Copower2 (contramap1 f fab) x

instance Copower2 =| Nat where
  adj1 = dimap (\f a -> nat2 $ \e -> runNat (runNat f) (Copower2 e a))
              (\f -> nat2 $ \(Copower2 e a) -> runNat2 (f a) e)

instance Copower2 e -| Nat e where
  adj = adj1

class (Profunctor (Power :: * -> j -> j), k ~ (~>)) => Powered (k :: j -> j -> *) | j -> k where
  type Power :: * -> j -> j
  -- | Power _ b -| (_ ~> b) a contravariant adjunction
  _Power :: forall (u :: *) (u' :: *) (a :: j) (a' :: j) (b :: j) (b' :: j).
             Iso (a ~> Power u b) (a' ~> Power u' b') (u -> (a ~> b)) (u' -> (a' ~> b'))

-- powers are traditionally denoted ⋔ in prefix, but ⋔ is an operator
infixr 0 ⋔
type (⋔) = Power

flip :: Powered k => (a ~> u ⋔ b) -> u -> k a b
flip = get _Power

unflip :: Powered k => (u -> k a b) -> a ~> u ⋔ b
unflip = unget _Power

instance Powered (->) where
  type Power = (->)
  _Power = dimap Prelude.flip Prelude.flip

newtype Power1 v f a = Power { runPower :: v -> f a }

instance Contravariant Power1 where
  contramap f = nat2 $ Power . lmap f . runPower

instance Functor (Power1 v) where
  fmap f = Nat $ Power . fmap1 (runNat f) . runPower

instance Semimonoidal (Power1 v) where
  ap2 = Nat $ \(Lift (Power va, Power vb)) -> Power $ \v -> Lift (va v, vb v)

instance Monoidal (Power1 v) where
  ap0 = Nat $ \(Const ()) -> Power $ \v -> Const ()

instance Semigroup m => Semigroup (Power1 v m) where
  mult = multM

instance Monoid m => Monoid (Power1 v m) where
  one = oneM

instance Semimonoidal f => Semimonoidal (Power1 v f) where
  ap2 (Power vfa, Power vfb) = Power $ \v -> ap2 (vfa v, vfb v)

instance Monoidal f => Monoidal (Power1 v f) where
  ap0 () = Power $ \_ -> ap0 ()

instance (Semimonoidal f, Semigroup m) => Semigroup (Power1 v f m) where
  mult = multM

instance (Monoidal f, Monoid m) => Monoid (Power1 v f m) where
  one = oneM

instance Functor f => Functor (Power1 v f) where
  fmap f = Power . fmap1 (fmap f) . runPower

-- Nat :: (i -> *) is powered over Hask
instance Powered (Nat :: (i -> *) -> (i -> *) -> *) where
  type Power = Power1
  _Power = dimap
     (\k v -> Nat $ \f -> runPower (runNat k f) v)
     (\k -> Nat $ \a' -> Power $ \u' -> runNat (k u') a')

-- * Kan extensions

-- Lan g -| Up g -| Ran g
type family Lan  :: (i -> j) -> (i -> k) -> j -> k
type family Ran  :: (i -> j) -> (i -> k) -> j -> k

type instance Ran = Ran0
newtype Ran0 (f :: i -> j) (g :: i -> *) (a :: j) = Ran { runRan :: forall r. (a ~> f r) ⋔ g r }

-- instance Up1 g -| Ran1 g

-- alternately, by universal property
-- data Ran f g a = forall z. Functor z => Ran (forall x. z (f x) ~> g x) (z a)

instance Category ((~>) :: j -> j -> *) => Contravariant (Ran0 :: (i -> j) -> (i -> *) -> j -> *) where
  contramap (Nat f) = nat2 $ \(Ran k) -> Ran $ k . (f .)

instance Category (Cod f) => Functor (Ran0 f) where
  fmap (Nat f) = Nat $ \(Ran k) -> Ran $ f . k

type instance Ran = Ran1
newtype Ran1 f g a x = Ran1 { runRan2 :: forall r. ((a ~> f r) ⋔ g r) x }

type instance Lan = Lan0
data Lan0 f g a where
  Lan :: Copower (g b) (f b ~> a) -> Lan0 f g a

type instance Lan = Lan1
data Lan1 f g a x where
  Lan1 :: Copower (g b) (f b ~> a) x -> Lan1 f g a x

-- newtype Codensity f a = Codensity { runCodensity :: forall r. f r^a ~> f r }
-- newtype Yoneda f a = Yoneda { runYoneda :: forall r. r^a ~> f r }

-- * Work in progress

-- constraints can be upgraded to a cartesian closed category with reflection

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
  contramap f = Nat $ unget _Sub $ un _Implies (. f)

instance Functor ((|-) p) where
  fmap f = unget _Sub $ un _Implies (f .)

instance (&) =| (|-) where
  adj1 = ccc

instance (&) p -| (|-) p where
  adj = ccc

instance CCC (:-) where
  type Exp = (|-)
  curried = dimap (\q -> fmap q . unapplyConstraint) (\p -> applyConstraint . first p) where
    applyConstraint :: forall p q. (p |- q & p) :- q
    applyConstraint = Sub $ Dict \\ (implies :: p :- q)
    unapplyConstraint :: p :- q |- (p & q)
    unapplyConstraint = Sub $ get _Implies (Sub Dict)

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
  fmap = contramap . inverse

instance Contravariant (Unit a) where
  contramap = fmap . inverse

instance Symmetric Unit where
  swap = inverse


-- * The initial "empty" category

data Empty (a :: Void) (b :: Void) = Empty (Empty a b)

instance Category Empty where
  id = Empty id
  (.) f = f `Prelude.seq` spin f where spin (Empty f) = spin f

instance Symmetric Empty where
  swap = inverse

instance Contravariant Empty where
  contramap f = Nat (. f)

instance Functor Empty where
  fmap = contramap . inverse

instance Functor (Empty a) where
  fmap = (.)

instance Contravariant (Empty a) where
  contramap = fmap . inverse

-- No :: Void -> *
data No (a :: Void)

instance Functor No where
  fmap !f = Prelude.undefined

infixr 9 ·
type g · f = Up f g

class (Category ((~>) :: k -> k -> *), Up ~ up) => Composed (up :: (i -> j) -> (j -> k) -> i -> k) | i j k -> up where
  type Up :: (i -> j) -> (j -> k) -> i -> k
  -- can't put the iso in here due to ghc #9200
  -- Composed is used to define Functor1, Functor1 is used in Profunctor, Profunctor is used in Iso
  -- but we recurse polymorphically during the cycle
  up    :: g (f a) ~> up f g a
  runUp :: up f g a ~> g (f a)

_Up :: Composed up => Iso (up f g a) (up f' g' a') (g (f a)) (g' (f' a'))
_Up = dimap runUp up

newtype Up1 f g a = Up (g (f a))
newtype Up2 f g a b = Up2 (g (f a) b)

instance Composed Up1 where
  type Up = Up1
  up = Up
  runUp (Up a) = a

instance Composed Up2 where
  type Up = Up2
  up = Nat Up2
  runUp = Nat $ \(Up2 a) -> a

class g (f a) => UpC f g a
instance g (f a) => UpC f g a

instance Composed UpC where
  type Up = UpC
  up = Sub Dict
  runUp = Sub Dict

instance Functor (Up1 f) where fmap f = Nat $ _Up (runNat f)
instance Functor (Up2 f) where fmap f = Nat $ _Up (runNat f)
instance Functor (UpC f) where fmap f = Nat $ _Up (runNat f)

-- functors over the second argument as indexed functors

class Limit (Up p Functor) => Functor1 p
instance Limit (Up p Functor) => Functor1 p

fmap1 :: forall p a b c. Functor1 p => (a ~> b) -> p c a ~> p c b
fmap1 f = case (limitDict :: Dict (Up p Functor c)) of Dict -> fmap f

-- contravariant functors over the second argument as indexed functors

class Limit (Up p Contravariant) => Contravariant1 p
instance Limit (Up p Contravariant) => Contravariant1 p

contramap1 :: forall p a b c. Contravariant1 p => (a ~> b) -> p c b ~> p c a
contramap1 f = case (limitDict :: Dict (Up p Contravariant c)) of Dict -> contramap f

class (Contravariant1 p, Functor1 p) => Phantom1 p
instance (Contravariant1 p, Functor1 p) => Phantom1 p

-- indexed monoidal functors

class Limit (Up p Semimonoidal) => Semimonoidal1 p
instance Limit (Up p Semimonoidal) => Semimonoidal1 p

ap2_1 :: forall p e a b. Semimonoidal1 p => p e a * p e b ~> p e (a * b)
ap2_1 = case limitDict :: Dict (Up p Semimonoidal e) of Dict -> ap2

class Limit (Up p Monoidal) => Monoidal1 p
instance Limit (Up p Monoidal) => Monoidal1 p

ap0_1 :: forall p e. Monoidal1 p => One ~> p e One
ap0_1 = case limitDict :: Dict (Up p Monoidal e) of Dict -> ap0

class Limit (Up p Cosemimonoidal) => Cosemimonoidal1 p
instance Limit (Up p Cosemimonoidal) => Cosemimonoidal1 p

op2_1 :: forall p e a b. Cosemimonoidal1 p => p e (a + b) ~> p e a + p e b
op2_1 = case limitDict :: Dict (Up p Cosemimonoidal e) of Dict -> op2

class Limit (Up p Comonoidal) => Comonoidal1 p
instance Limit (Up p Comonoidal) => Comonoidal1 p

op0_1 :: forall p e. Comonoidal1 p => p e Zero ~> Zero
op0_1 = case limitDict :: Dict (Up p Comonoidal e) of Dict -> op0

-- * Groupoids

class Category c => Groupoid c where
  inverse :: c a b -> c b a

instance Groupoid ((~>) :: j -> j -> *) => Groupoid (Nat :: (i -> j) -> (i -> j) -> *) where
  inverse (Nat f) = Nat (inverse f)

instance (Groupoid ((~>) :: i -> i -> *), Groupoid ((~>) :: j -> j -> *)) =>
  Groupoid (Prod :: (i, j) -> (i, j) -> *) where
  inverse Want = Want
  inverse (Have f g) = Have (inverse f) (inverse g)

instance Groupoid Empty where
  inverse !f = Empty (inverse f)

instance Groupoid Unit where
  inverse Unit = Unit

-- * Representability

class Representable (p :: x -> y -> *) where
  type Rep p :: y -> x
  _Rep :: Iso (p a b) (p a' b') (a ~> Rep p b) (a' ~> Rep p b')

instance Representable (->) where
  type Rep (->) = Id
  _Rep = un (mapping _Id)

instance Representable (Nat :: (i -> *) -> (i -> *) -> *) where
  type Rep (Nat :: (i -> *) -> (i -> *) -> *) = Id
  _Rep = un (mapping _Id)

instance Representable (:-) where
  type Rep (:-) = Id
  _Rep = un (mapping _Id)

class Corepresentable (p :: x -> y -> *) where
  type Corep p :: x -> y
  _Corep :: Iso (p a b) (p a' b') (Corep p a ~> b) (Corep p a' ~> b')

instance Corepresentable (->) where
  type Corep (->) = Id
  _Corep = lmapping _Id

instance Corepresentable (Nat :: (i -> *) -> (i -> *) -> *) where
  type Corep (Nat :: (i -> *) -> (i -> *) -> *) = Id
  _Corep = lmapping _Id

instance Corepresentable (:-) where
  type Corep (:-) = Id
  _Corep = lmapping _Id

-- a semigroupoid/semicategory looks like a "self-enriched" profunctor
-- when we put no other constraints on p

class    (Profunctor p, p ~ (~>)) => Semicategory p
instance (Profunctor p, p ~ (~>)) => Semicategory p

infixr |=

-- |
-- @(|=) :: Constrained -> * -> *@

-- This is a corepresentable functor
newtype p |= q = Constrained { runConstrained :: p => q }

instance Contravariant (|=) where
  contramap ab = Nat $ \bc -> Constrained $ case ab of
    Sub Dict -> runConstrained bc

instance Functor ((|=) e) where
  fmap bc ab = Constrained $ bc (runConstrained ab)

instance Semimonoidal ((|=) e) where
  ap2 (ea,eb) = Constrained $ (runConstrained ea, runConstrained eb)

instance Monoidal ((|=) e) where
  ap0 () = Constrained ()

-- we can make an indexed adjunction for this
instance Corepresentable (|=) where
  type Corep (|=) = Dict
  _Corep = dimap (\ab Dict -> case ab of Constrained b -> b) (\ab -> Constrained $ ab Dict)

data EnvC p q = EnvC (Dict p) q

-- EnvC p (Either a b) -> Either (EnvC p a) (EnvC p b)

instance Functor EnvC where
  fmap f = Nat $ \(EnvC p q) -> EnvC (fmap f p) q

instance Functor (EnvC p) where
  fmap f (EnvC p q) = EnvC p (f q)

instance Cosemimonoidal (EnvC p) where
  op2 (EnvC p eab) = bimap (EnvC p) (EnvC p) eab

instance Comonoidal (EnvC p) where
  op0 (EnvC _ v) = v

-- all constraints are semimonoids
instance Semimonoidal (EnvC p) where
  ap2 (EnvC Dict p, EnvC Dict q) = EnvC Dict (p, q)

instance Monoid p => Monoidal (EnvC p) where
  ap0 = EnvC (Dict \\ (one :: () :- p))

instance EnvC =| (|=) where
  adj1 = dimap (\eab a -> Constrained $ eab (EnvC Dict a))
               (\aeb (EnvC Dict a) -> runConstrained (aeb a))

instance EnvC e -| (|=) e where
  adj = adj1
