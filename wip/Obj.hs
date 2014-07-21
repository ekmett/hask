{-# LANGUAGE TypeOperators, PolyKinds, TypeFamilies, RankNTypes, GADTs, NoImplicitPrelude, ConstraintKinds, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, DataKinds, ScopedTypeVariables, DefaultSignatures, FunctionalDependencies #-}
module Obj where

import Prelude (($), undefined, Bool(..))
import Data.Constraint ((:-)(..), Dict(..), Constraint, Class(..), (:=>)(..), (\\))
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy(..))

infixr 0 `Hom`, ~>, |-
type family Hom :: i -> i -> j
type instance Hom = (->)  -- @* -> * -> *@
type instance Hom = (:-)  -- @Constraint -> Constraint -> *@
type instance Hom = (|-)  -- @i -> i -> Constraint@ -- can we lift this condition by requiring the base case be Constraint?
type instance Hom = Nat   -- @(i -> j) -> (i -> j) -> *@
type (~>) = (Hom :: i -> i -> *)
type Arr (a :: i) = (Hom :: i -> i -> *)
type Dom (f :: i -> j) = (Hom :: i -> i -> *)
type Cod (f :: i -> j) = (Hom :: i -> i -> *)
type Cod2 (p :: i -> j -> k) = (Hom :: k -> k -> *)

type family Irrelevant (k :: i -> i -> *) :: Bool
type instance Irrelevant (->) = False
type instance Irrelevant (:-) = True
type instance Irrelevant (Nat :: (i' -> j') -> (i' -> j') -> *) = Irrelevant (Hom :: j' -> j' -> *)
type instance Irrelevant Unit = True
-- use products

class Vacuous a
instance Vacuous a

class Objective (f :: i -> j) where
  obj :: Obj a :- Obj (f a)
  default obj :: Obj (f a) => Obj a :- Obj (f a)
  obj = Sub Dict

instance Objective Vacuous
instance Objective (~)
instance Objective ((~) a)
instance Objective Dict

data Unit a b where
  Unit :: Unit '() '()
type instance Hom = Unit

data Nat (f :: i -> j) (g :: i -> j) where
  Nat :: (Objective f, Objective g) => { runNat :: forall a. Obj a => f a ~> g a } -> Nat f g

nat :: (Objective f, Objective g) => (forall a. Obj a => Proxy a -> f a ~> g a) -> Nat f g
nat k = Nat (k Proxy)

sub :: (a => Proxy a -> Dict b) -> a :- b
sub k = Sub (k Proxy)

-- runNat :: Obj a => Nat f g -> f a ~> g a
-- runNat (Nat f) = f

-- allow the embedding of (natural transformations over) constraint implications into constraint.
class Irrelevant (Arr p) ~ True => p |- q where
  implies :: p ~> q

-- BEGIN INCOHERENT
instance Vacuous   |- ComposeC Functor (->) where implies = Nat (Sub Dict)
instance Vacuous   |- ComposeC Functor (:-) where implies = Nat (Sub Dict)
instance (~) '()   |- ComposeC Functor Unit where implies = Nat (Sub Dict)
instance Category (Arr r) => Vacuous |- ComposeC Functor (Beget r) where implies = Nat (Sub Dict)
instance Category (Hom :: j -> j -> *) =>
  (Objective |- ComposeC Functor (Nat :: (i -> j) -> (i -> j) -> *)) where implies = Nat (Sub Dict)
instance (Irrelevant (Hom :: i -> i -> *) ~ True, Category (Hom :: i -> i -> *), h ~ Obj) => h |- ComposeC Functor ((|-) :: i -> i -> Constraint) where implies = Nat (Sub Dict)
-- END INCOHERENT  


-- you can provide many incoherent instances for p |- q

instance Objective Nat
instance Objective Objective
instance Objective (Nat f)
instance Objective (|-)
instance Objective ((|-) p)
  
class Objective f => Functor (f :: i -> j) where
  fmap :: (a ~> b) -> f a ~> f b

instance Category (Hom :: j -> j -> *) => Functor (Objective :: (i -> j) -> Constraint) where
  fmap f = Sub $ target f
instance Objective Functor
instance Functor Vacuous where fmap _ = Sub Dict
instance Functor Dict where
  fmap f Dict = case f of
    Sub Dict -> Dict

class Objective f => Contravariant (f :: i -> j) where
  contramap :: (a ~> b) -> f b ~> f a

instance Contravariant Vacuous where contramap _ = Sub Dict

type family Obj :: i -> Constraint
type instance Obj = (Vacuous   :: *          -> Constraint)
type instance Obj = (Vacuous   :: Constraint -> Constraint)
type instance Obj = Objective
type instance Obj = (~) '() -- :: () -> Constraint



class (Obj |- p) => LimC p
instance (Obj |- p) => LimC p
instance Obj ~ h => Class (h |- p) (LimC p) where cls = Sub Dict
instance Obj ~ h => (h |- p) :=> LimC p where ins = Sub Dict

instance Objective LimC where obj = Sub Dict

class    f (g a) => ComposeC f g a
instance f (g a) => ComposeC f g a
instance Class (f (g a)) (ComposeC f g a) where cls = Sub Dict
instance f (g a) :=> ComposeC f g a where ins = Sub Dict

instance Objective ComposeC where obj = Sub Dict
instance Objective f => Objective (ComposeC f) where obj = Sub Dict
instance (Objective f, Objective g) => Objective (ComposeC f g) where obj = Sub Dict

class LimC (ComposeC p f) => Post p f
instance LimC (ComposeC p f) => Post p f

fmap1 :: forall p a b x. (Post Functor p, Obj x) => (a ~> b) -> p x a ~> p x b
fmap1 = case runNat implies :: Obj x :- ComposeC Functor p x of
  Sub Dict -> fmap

contramap1 :: forall p a b x. (Post Contravariant p, Obj x) => (a ~> b) -> p x b ~> p x a
contramap1 = case runNat implies :: Obj x :- ComposeC Contravariant p x of
  Sub Dict -> contramap

-- we need Post
class (Contravariant p, Post Functor p) => Profunctor p
instance (Contravariant p, Post Functor p) => Profunctor p

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

class (Profunctor hom, hom ~ Hom, Functor (Obj :: i -> Constraint)) => Category (hom :: i -> i -> *) where
  id  :: Obj a => hom a a
  (.) :: hom b c -> hom a b -> hom a c
  source :: hom a b -> Dict (Obj a)
  target :: hom a b -> Dict (Obj b)

instance Objective (->)
instance Contravariant (->) where contramap f = Nat (. f)
instance Objective ((->) a) 
instance Functor ((->) a) where fmap = (.)
instance Category (->) where
  id x = x
  (.) f g x = f (g x)
  source _ = Dict
  target _ = Dict

instance Objective Unit
instance Contravariant Unit where contramap f = Nat (. f)
instance Objective (Unit a)
instance Functor (Unit a) where fmap = (.)
instance Functor ((~) '()) where fmap Unit = id
instance Category Unit where
  id = Unit
  Unit . Unit = Unit
  source Unit = Dict
  target Unit = Dict

instance Objective (:-)
instance Contravariant (:-) where contramap f = Nat (. f)
instance Objective ((:-) a) 
instance Functor ((:-) a) where fmap = (.)
instance Category (:-) where
  id = Sub Dict
  f . g = Sub $ Dict \\ f \\ g
  source _ = Dict
  target _ = Dict

lmap f = runNat (contramap f)

dimap :: (Profunctor (p :: i -> j -> k), Category (Hom :: i -> i -> *), Category (Hom :: j -> j -> *), Category (Hom :: k -> k -> *)) => (a ~> b) -> (c ~> d) -> p b c ~> p a d
dimap f g = case target g of 
  Dict -> case target f of
    Dict -> runNat (contramap f) . fmap1 g 

_Sub :: Iso (a :- b) (c :- d) (Dict a -> Dict b) (Dict c -> Dict d)
_Sub = dimap (\pq Dict -> case pq of Sub q -> q) (\f -> Sub $ f Dict)

newtype Magic a b c = Magic ((a |- b) => c)

_Implies :: (Irrelevant (Arr c) ~ True) => Iso (Dict (a |- b)) (Dict (c |- d)) (a ~> b) (c ~> d)
_Implies = dimap (\Dict -> implies) (reify Dict) where
  reify :: forall a b c. ((a |- b) => c) -> (a ~> b) -> c
  reify k = unsafeCoerce (Magic k :: Magic a b c)

newtype Get (r :: i) (a :: i) (b :: i) = Get { runGet :: a ~> r }
_Get :: Iso (Get r a b) (Get s c d) (a ~> r) (c ~> s)
_Get = dimap runGet Get

instance Objective Get
instance Category (Hom :: i -> i -> *) => Functor (Get :: i -> i -> i -> *) where fmap f = Nat $ Nat $ _Get (f .)
instance Objective (Get r)
instance Category (Arr r) => Contravariant (Get r) where contramap f = Nat $ _Get (. f)
instance Objective (Get r a)
instance Functor (Get r a) where fmap _ = Get . runGet
instance Contravariant (Get r a) where contramap _ = Get . runGet

get :: (Category (Arr a), Obj a) => (Get a a a -> Get a s s) -> s ~> a
get l = runGet $ l (Get id)

newtype Beget (r :: i) (a :: i) (b :: i) = Beget { runBeget :: r ~> b }
instance Objective Beget
instance Category (Hom :: i -> i -> *) => Contravariant (Beget :: i -> i -> i -> *) where contramap f = Nat $ Nat $ _Beget (. f)
instance Objective (Beget r)
instance Functor (Beget r) where fmap _ = Nat $ Beget . runBeget
instance Contravariant (Beget r) where contramap _ = Nat $ Beget . runBeget
instance Objective (Beget r a)
instance Category (Hom :: i -> i -> *) => Functor (Beget r a :: i -> *) where fmap f = _Beget (f .)

_Beget :: Iso (Beget r a b) (Beget s c d) (r ~> b) (s ~> d)
_Beget = dimap runBeget Beget

beget :: (Category (Arr b), Obj b) => (Beget b b b -> Beget b t t) -> b ~> t
beget l = runBeget $ l (Beget id)

instance (Irrelevant (Hom :: i -> i -> *) ~ True, Category (Hom :: i -> i -> *)) => Contravariant ((|-) :: i -> i -> Constraint) where
  contramap f = Nat $ beget _Sub $ _Implies (. f)

instance (Irrelevant (Hom :: i -> i -> *) ~ True, Category (Hom :: i -> i -> *)) => Functor ((|-) p :: i -> Constraint) where
  fmap f = beget _Sub $ _Implies (f .)
  
instance Objective (Obj :: i -> Constraint) => Functor (LimC :: (i -> Constraint) -> Constraint) where
  fmap f = ins . fmap1 f . cls

instance Functor (ComposeC :: (j -> Constraint) -> (i -> j) -> (i -> Constraint)) where
  fmap (Nat f) = nat $ \(Proxy :: Proxy f) -> nat $ \(Proxy :: Proxy a) -> _Compose $ 
    case obj :: Obj a :- Obj (f a) of
      Sub Dict -> f 

instance (Category (Cod f), Functor f) => Functor (ComposeC f) where
  fmap (Nat f) = Nat $ _Compose $ fmap f

instance Contravariant f => Contravariant (ComposeC f) where
  contramap (Nat f) = Nat $ _Compose $ contramap f

class Category hom => Composed (hom :: k -> k -> *) where
  type Compose :: (j -> k) -> (i -> j) -> i -> k
  compose :: f (g a) `hom` Compose f g a 
  decompose :: Compose f g a `hom` f (g a)

instance Composed (:-) where
  type Compose = ComposeC
  compose = Sub Dict
  decompose = Sub Dict

_Compose :: Composed (Hom :: k -> k -> *) => Iso (Compose (f :: j -> k) g a) (Compose (h :: j -> k) i b) (f (g a)) (h (i b))
_Compose = dimap decompose compose

-- * Constraints

class a => ConstC a b
instance a => ConstC a b
instance Class a (ConstC a b) where cls = Sub Dict
instance a :=> ConstC a b where ins = Sub Dict


class hom ~ Hom => Complete (hom :: j -> j -> *) where
  type Lim :: (i -> j) -> j
  type Const :: j -> i -> j
  elim :: Obj a => hom (Lim g) (g a)

  _Const :: (Obj a, Obj b, Obj c, Obj d) => Iso (Const a b) (Const c d) (a :: j) (c :: j)
  complete :: Dict (Const -| (Lim :: (i -> j) -> j))
  -- default complete :: (Const -| (Lim :: (i -> j) -> j)) => Dict (Const -| (Lim :: (i-> j) -> j))
  -- complete = Dict

instance Objective ConstC where obj = Sub Dict
instance Functor ConstC where
  fmap f = Nat $ Sub $ Dict \\ f

instance Objective (ConstC a) where obj = Sub Dict
instance Functor (ConstC a) where fmap _ = Sub Dict
instance Contravariant (ConstC a) where contramap _ = Sub Dict

instance Category (Hom :: i -> i -> *) => (ConstC :: Constraint -> i -> Constraint) -| (LimC :: (i -> Constraint) -> Constraint) where
{-
  adj = dimap hither undefined where
    hither :: Nat (ConstC a) f -> a :- LimC f
    hither (Nat f) = Sub $ fmap ins $ beget _Implies $ Nat $ Sub $ fmap f Dict
-}




instance Complete (:-) where
  type Lim = LimC
  type Const = ConstC
  -- complete = Dict

newtype Const1 a b = Const { getConst :: a }

instance Objective Const1 where
  obj = Sub Dict
instance Functor Const1 where
  fmap f = Nat $ Const . f . getConst

instance Objective (Const1 a) where
  obj = Sub Dict

instance Objective Lim1
instance Functor Lim1
instance Const1 -| Lim1 where
  adj = dimap (\f a -> Lim (runNat f (Const a))) $ \h -> Nat $ getLim . h . getConst

instance Complete (->) where
  type Lim = Lim1
  type Const = Const1

newtype Lim1 (p :: i -> *) = Lim { getLim :: forall a. Obj a => p a }

instance Contravariant Nat  where contramap = undefined -- TODO
instance Category (Hom :: j -> j -> *) => Functor (Nat f :: (i -> j) -> *) where fmap = undefined -- TODO
instance Category (Hom :: j -> j -> *) => Category (Nat :: (i -> j) -> (i -> j) -> *) where
  id = Nat id1
  source (Nat f) = Dict
  target (Nat f) = Dict
  Nat f . Nat g = Nat (f . g)

id1 :: forall hom f x. (Category (hom :: j -> j -> *), Objective f, Obj x) => hom (f x) (f x)
id1 = id \\ (obj :: Obj x :- Obj (f x))

class (Functor p, Post Functor p) => Bifunctor p
instance (Functor p, Post Functor p) => Bifunctor p

class (Functor f, Functor u) => (f :: j -> i) -| (u :: i -> j) | f -> u, u -> f where
  adj :: (Obj a, Obj b, Obj c, Obj d) => Iso (f a ~> b) (f c ~> d) (a ~> u b) (c ~> u d)
  -- adj :: Iso' (Up f) (Down u)

class Curried p q | p -> q, q -> p where
  curried :: (Obj a, Obj b, Obj c, Obj d, Obj e, Obj f) => Iso (p a b ~> c) (p d e ~> f) (a ~> q b c) (d ~> q e f)
