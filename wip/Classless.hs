{-# LANGUAGE TypeOperators, PolyKinds, TypeFamilies, RankNTypes, GADTs, NoImplicitPrelude, ConstraintKinds, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances, DataKinds, ScopedTypeVariables, DefaultSignatures, FunctionalDependencies, EmptyCase, OverlappingInstances, IncoherentInstances #-}
module Obj where

import Prelude (($), undefined, Bool(..))
import Data.Constraint ((:-)(..), Dict(..), Constraint, Class(..), (:=>)(..), (\\), trans, refl)
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy(..))
import Data.Void
import GHC.Prim (Any)


todo :: a
todo = undefined

infixr 0 `Hom`, ~>

type family Hom :: i -> i -> j
type instance Hom = (->)    -- @* -> * -> *@
type instance Hom = (:-)    -- @Constraint -> Constraint -> *@

type (~>) = (Hom :: i -> i -> *)
type Arr (a :: i) = (Hom :: i -> i -> *)
type Dom (f :: i -> j) = (Hom :: i -> i -> *)
type Cod (f :: i -> j) = (Hom :: i -> i -> *)
type Cod2 (p :: i -> j -> k) = (Hom :: k -> k -> *)

--------------------------------------------------------------------------------
-- * Ob
--------------------------------------------------------------------------------

class Vacuous a
instance Vacuous a

type family Ob :: i -> Constraint
type instance Ob = (Vacuous :: * -> Constraint)
type instance Ob = (Vacuous :: Constraint -> Constraint)

--------------------------------------------------------------------------------
-- * Discrete
--------------------------------------------------------------------------------


-- A discrete functor @(f :: i -> j)@ is a functor from the discrete category of i.
-- That is to say it takes objects to objects and identity arrows to identity arrows.
--
-- @
-- instance (Ob f, Ob a) => Ob (f a)
-- @
class Discrete (f :: i -> j) where
  ob :: Ob a :- Ob (f a)
  default ob :: Ob (f a) => Ob a :- Ob (f a)
  ob = Sub Dict

type instance Ob = Discrete -- :: (i -> j) -> Constraint

-- Incoherent
instance Discrete (f :: i -> Constraint) -- subsumes instance Discrete Discrete
instance Discrete (f :: i -> *)
-- /Incoherent
instance Discrete (~)
instance Discrete (->)
instance Discrete (:-)

data Nat (h :: j -> k -> *) (f :: i -> j) (g :: i -> k) where
  Nat :: (Ob f, Ob g) => { runNat :: forall a. Ob a => h (f a) (g a) }  -> Nat h f g

nat :: (Ob f, Ob g) => (forall a. Ob a => Proxy a -> p (f a) (g a)) -> Nat p f g
nat k = Nat (k Proxy)

-- ob is closed
apOb :: forall f a. (Ob f, Ob a) :- Ob (f a)
apOb = Sub $ Dict \\ (ob :: Ob a :- Ob (f a))

type instance Hom = Nat Hom -- @(i -> j) -> (i -> j) -> *@

instance Discrete Nat
instance Discrete (Nat hom)


--------------------------------------------------------------------------------
-- * Functor
--------------------------------------------------------------------------------

class Discrete f => Functor f where
  fmap :: (a ~> b) -> f a ~> f b

instance Functor Vacuous where
  fmap _ = Sub Dict

instance Functor Discrete where
  fmap Nat{} = Sub Dict

--------------------------------------------------------------------------------
-- * Contravariant
--------------------------------------------------------------------------------

class Discrete f => Contravariant f where
  contramap :: (a ~> b) -> f b ~> f a

instance Contravariant Vacuous where
  contramap _ = Sub Dict

instance Contravariant Discrete where
  contramap Nat{} = Sub Dict

instance Contravariant (:-) where contramap ab = Nat (`trans` ab)
instance Contravariant (->) where contramap ab = Nat (\bc a -> bc (ab a))

--------------------------------------------------------------------------------
-- * Thin
--------------------------------------------------------------------------------

type family (p :: Bool) && (q :: Bool) :: Bool where
  False && q = False
  True  && q = q

-- indicate if there is only a single arrow between any two objects in a given category
type family Thin (hom :: i -> i -> *) :: Bool
type instance Thin (->) = False
type instance Thin (:-) = True
type instance Thin (Nat hom) = Thin hom

infixr 0 |-
class Thin (Arr p) ~ True => p |- q where
  impl :: p ~> q

--------------------------------------------------------------------------------
-- * Limits of Constraints
--------------------------------------------------------------------------------

data LIM = Lim
type Lim = (Any 'Lim :: (i -> j) -> j)

instance Ob ~ h => Class (h |- p) (Lim p) where cls = unsafeCoerceConstraint
instance Ob ~ h => (h |- p) :=> Lim p where ins = unsafeCoerceConstraint

--------------------------------------------------------------------------------
-- * Compose
--------------------------------------------------------------------------------

data COMPOSE = Compose
type Compose = (Any 'Compose :: (j -> k) -> (i -> j) -> i -> k)

instance Class (f (g a)) (Compose f g a) where cls = unsafeCoerceConstraint
instance f (g a) :=> Compose f g a where ins = unsafeCoerceConstraint

class (hom ~ Hom) => Composed (hom :: k -> k -> *) where
  obCompose   :: forall (f :: j -> k). Ob f :- Ob (Compose f :: (i -> j) -> i -> k)
  obCompose1  :: forall (f :: j -> k) (g :: i -> j). Ob f => Ob g :- Ob (Compose f g :: i -> k)
  obCompose2  :: forall (f :: j -> k) (g :: i -> j) (a :: i). (Ob f, Ob g) => Ob a :- Ob (Compose f g a :: k)
  compose     :: f (g a) `hom` Compose f g a
  decompose   :: Compose f g a `hom` f (g a)

instance Composed (->) where
  obCompose  = Sub Dict
  obCompose1 = Sub Dict
  obCompose2 = Sub Dict
  compose    = unsafeCoerce
  decompose  = unsafeCoerce

instance Composed (:-) where
  obCompose  = Sub Dict
  obCompose1 = Sub Dict
  obCompose2 = Sub Dict
  compose    = ins
  decompose  = cls

instance Composed hom => Composed (Nat hom) where
  obCompose = Sub Dict
  obCompose1 = Sub Dict
  obCompose2 = todo
  compose    = todo
  decompose  = todo

instance Composed (Hom :: k -> k -> *) => Discrete (Compose :: (j -> k) -> (i -> j) -> (i -> k)) where
  ob = obCompose

instance (Composed (Hom :: k -> k -> *), Ob f) => Discrete (Compose (f :: j -> k) :: (i -> j) -> i -> k) where
  ob = obCompose1

instance (Composed (Hom :: k -> k -> *), Ob f, Ob g) => Discrete (Compose (f :: j -> k) (g :: i -> j) :: i -> k) where
  ob = obCompose2


{-
instance Composed (Hom :: k -> k -> *) => Functor (Compose :: (j -> k) -> (i -> j) -> i -> k) where
  fmap :: (f ~> g) -> Compose f ~> Compose g
  fmap (Nat f) = nat $ \(Proxy :: Proxy f) -> nat $ \(Proxy :: Proxy a) -> _Compose $
    case ob :: Ob a :- Ob (f a) of
      Sub Dict -> f
-}


{-
instance (Composed (Cod f), Functor f) => Functor (Compose f) where
  fmap (Nat f) = Nat $ _Compose $ fmap f

instance (Composed (Cod f), Contravariant f) => Contravariant (Compose f) where
  contramap (Nat f) = Nat $ _Compose $ contramap f
-}


{-
instance (Composed (Cod f), Functor f, Functor g) => Functor (Compose f g :: i -> k) where
  fmap f = _Compose $ fmap (fmap f)

instance (Composed (Cod f), Contravariant f, Functor g) => Contravariant (Compose f g :: i -> k) where
  contramap f = _Compose $ contramap (fmap f)
-}  



{-

class Contravariant f => Profunctor (f :: i -> j -> k) where
  dimap :: (a ~> b) -> (c ~> d) -> f b c ~> f a d

instance Profunctor (->) where
  dimap f g h x = g (h (f x))

instance Profunctor (:-) where
  dimap f g h = g . h . f

class Functor f => Bifunctor f where
  bimap :: (a ~> b) -> (c ~> d) -> f a c -> f b d

instance Functor Nat

instance Contravariant p => Contravariant (Nat p) where
  -- contramap (Nat f) = Nat (contramap f)

-- really wants functor in the second argument given Discrete f
instance Profunctor p => Functor (Nat p f) where
  fmap = (.)

  contramap = go where

    go :: forall f g. (f ~> g) -> Nat p g ~> Nat p f
    go (Nat oab oba ab) = nat (Sub Dict) (Sub Dict) $ \(Proxy :: Proxy h) (Nat obc ocb bc) -> nat todo todo $ \(Proxy :: Proxy x) -> _heh -- runNat (contramap ab) bc \\ (ob :: Ob x :- Ob (h x) )

class (Functor f, Contravariant f) => Phantom f
instance (Functor f, Contravariant f) => Phantom f

class (hom ~ Hom, Profunctor hom, Phantom (Ob :: i -> Constraint)) => Category (hom :: i -> i -> *) where
  id  :: Ob a => hom a a
  (.) :: hom b c -> hom a b -> hom a c

  source :: hom a b -> Dict (Ob a)
  default source :: Ob a => hom a b -> Dict (Ob a)
  source _ = Dict

  target :: hom a b -> Dict (Ob b)
  default target :: Ob a => hom a b -> Dict (Ob b)
  target _ = Dict


instance Category (->) where
  id x = x
  (.) f g x = f (g x)

instance Category (:-) where
  id = Sub Dict
  f . g = Sub $ Dict \\ f \\ g

-- instance Profunctor hom => Profunctor (Nat hom) where
-- dimap (Nat oab oba ab) (Nat ocd odc cd) (Nat obc ocb bc) = Nat todo todo (cd . bc . ab)

instance Category hom => Category (Nat hom) where
  id = Nat id id id1 where
    id1 :: forall f x. (Discrete f, Ob x) => hom (f x) (f x)
    id1 = id \\ (ob :: Ob x :- Ob (f x))
  Nat obc ocb bc . Nat oab oba ab = Nat (obc . oab) (oba . ocb) (bc . ab)


-}
{-

--------------------------------------------------------------------------------
-- * Unit :: () -> () -> *
--------------------------------------------------------------------------------

class '() ~ a => UnitOb a
instance '() ~ a => UnitOb a

type instance Ob = UnitOb  -- :: () -> Constraint

data Unit a b where
  Unit :: Unit '() '()

type instance Hom = Unit -- @() -> () -> *@
type instance Preordered Unit = True

--------------------------------------------------------------------------------
-- * Empty :: Void -> Void -> *
--------------------------------------------------------------------------------

data Empty (a :: Void) (b :: Void)
type instance Hom = Empty -- @Void -> Void ->*@
type instance Preordered Empty = True

class EmptyOb (e :: Void) where no :: p e
type instance Ob = EmptyOb  -- :: Void -> Constraint

instance Functor EmptyOb where fmap f = case f of {}
instance Contravariant EmptyOb where contramap f = case f of {}

instance Discrete Empty

instance Contravariant Empty where
  contramap f = case f of {}

instance Functor Empty where
  fmap f = case f of {}

instance Contravariant (Empty a) where
  contramap f = case f of {}

instance Functor (Empty a) where
  fmap f = case f of {}


{-
data NO = No
type No = (Any 'No :: Void -> k)

instance Discrete No where
  ob = Sub $ fmap decompose $ decompose no

instance Functor No  where
  fmap f = case f of {}

instance Contravariant No where
  contramap f = case f of {}
-}

{- Prod

type instance Hom = Prod  -- @(i,j) -> (i,j) -> *@
type instance Ob = ProdOb   -- :: (i,j)     -> Constraint
type instance Preordered (Prod :: (i,j) -> (i,j) -> *) = Preordered (Hom :: i -> i -> *) && Preordered (Hom :: j -> j -> *)

data Prod p q where
  Prod :: (a ~> b) -> (c ~> d) -> Prod '(a,c) '(b,d)

type family Fst (p :: (i,j)) :: i where
  Fst '(a,b) = a

type family Snd (p :: (i,j)) :: j where
  Snd '(a,b) = b

class (p ~ '(Fst p, Snd p), Ob (Fst p), Ob (Snd p)) => ProdOb (p :: (i,j))
instance (p ~ '(Fst p, Snd p), Ob (Fst p), Ob (Snd p)) => ProdOb (p :: (i,j))

instance Discrete ProdOb

instance (Category (Hom :: i -> i -> *), Category (Hom :: j -> j -> *)) => Functor (ProdOb :: (i, j) -> Constraint) where
  fmap (Prod ab cd) = case target ab of
    Dict -> case target cd of
      Dict -> Sub Dict
instance (Category (Hom :: i -> i -> *), Category (Hom :: j -> j -> *)) => Contravariant (ProdOb :: (i, j) -> Constraint) where
  contramap (Prod ab cd) = case source ab of
    Dict -> case source cd of
      Dict -> Sub Dict

-}

{-

type instance Hom = (|-)  -- @i -> i -> Constraint@ -- can we lift this condition by requiring the base case be Constraint?

-}

{- Thin
class    (Category hom, Preordered hom ~ True) => Thin (hom :: i -> i -> *)
instance (Category hom, Preordered hom ~ True) => Thin hom

-}

class Thin (Arr p) ~ True => p |- q where
  implies :: p ~> q



{-



sub :: (a => Proxy a -> Dict b) -> a :- b
sub k = Sub (k Proxy)

-- BEGIN INCOHERENT
instance Vacuous   |- Compose Functor (->) where implies = Nat (Sub Dict)
instance Vacuous   |- Compose Functor (:-) where implies = Nat (Sub Dict)
instance (~) '()   |- Compose Functor Unit where implies = Nat (Sub Dict)
instance Category (Arr r) => Vacuous |- Compose Functor (Beget r) where implies = Nat (Sub Dict)
instance Category (Hom :: j -> j -> *) =>
  (Discrete |- Compose Functor (Nat :: (i -> j) -> (i -> j) -> *)) where implies = Nat (Sub Dict)
instance (Thin (Hom :: i -> i -> *), h ~ Ob) => h |- Compose Functor ((|-) :: i -> i -> Constraint) where implies = Nat (Sub Dict)
instance Discrete p => EmptyOb |- p where
  implies = Nat (Sub $ decompose no)
instance Discrete (f :: i -> Constraint) where ob = Sub Dict
instance Discrete (f :: i -> *) where ob = Sub Dict
-- END INCOHERENT

-- you can provide many incoherent instances for p |- q

instance Discrete Nat
instance Discrete (Nat p)
instance Discrete (|-)

class Discrete f => Functor (f :: i -> j) where
  fmap :: (a ~> b) -> f a ~> f b

instance Category (Hom :: j -> j -> *) => Functor (Discrete :: (i -> j) -> Constraint) where
  fmap f = Sub $ target f
instance Functor Vacuous where fmap _ = Sub Dict
instance Functor Dict where
  fmap f Dict = case f of
    Sub Dict -> Dict

class Discrete f => Contravariant (f :: i -> j) where
  contramap :: (a ~> b) -> f b ~> f a

instance Category (Hom :: j -> j -> *) => Contravariant (Discrete :: (i -> j) -> Constraint) where
  contramap f = Sub $ source f

instance Contravariant Vacuous where contramap _ = Sub Dict

class (p,q) => p & q
instance (p,q) => p & q
instance Discrete (&)
instance Functor (&) where fmap f = Nat (Sub $ Dict \\ f)
instance Functor ((&) p) where fmap f = Sub $ Dict \\ f

-- * Functor Composition


-- * Limit


-- * Post

class LimC (Compose p f) => Post p f
instance LimC (Compose p f) => Post p f

fmap1 :: forall p a b x. (Post Functor p, Ob x) => (a ~> b) -> p x a ~> p x b
fmap1 = case runNat implies :: Ob x :- Compose Functor p x of
  Sub Dict -> fmap

contramap1 :: forall p a b x. (Post Contravariant p, Ob x) => (a ~> b) -> p x b ~> p x a
contramap1 = case runNat implies :: Ob x :- Compose Contravariant p x of
  Sub Dict -> contramap

-- we need Post
class (Contravariant p, Post Functor p) => Profunctor p
instance (Contravariant p, Post Functor p) => Profunctor p

class (Functor p, Contravariant p) => Phantom p
instance (Functor p, Contravariant p) => Phantom p

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

class (Profunctor hom, hom ~ Hom, Phantom (Ob :: i -> Constraint)) => Category (hom :: i -> i -> *) where
  id  :: Ob a => hom a a
  (.) :: hom b c -> hom a b -> hom a c
  source :: hom a b -> Dict (Ob a)
  target :: hom a b -> Dict (Ob b)

instance Discrete (->)
instance Contravariant (->) where contramap f = Nat (. f)
instance Discrete ((->) a)
instance Functor ((->) a) where fmap = (.)
instance Category (->) where
  id x = x
  (.) f g x = f (g x)
  source _ = Dict
  target _ = Dict

instance Discrete Unit
instance Contravariant Unit where contramap f = Nat (. f)
instance Discrete (Unit a)
instance Functor (Unit a) where fmap = (.)
instance Functor ((~) '()) where fmap Unit = id
instance Contravariant ((~) '()) where contramap Unit = id
instance Category Unit where
  id = Unit
  Unit . Unit = Unit
  source Unit = Dict
  target Unit = Dict

instance Discrete Empty
instance Contravariant Empty where contramap f = case f of {}
instance Functor Empty where fmap f = case f of {}
instance Contravariant (Empty a) where contramap f = case f of {}
instance Discrete (Empty a) where ob = Sub Dict
instance Functor (Empty a) where fmap f = case f of {}
instance Category Empty where
  id = no
  source f = case f of {}
  target f = case f of {}
  f . _ = case f of {}

instance Discrete (:-)
instance Contravariant (:-) where contramap f = Nat (. f)
instance Discrete ((:-) a)
instance Functor ((:-) a) where fmap = (.)
instance Category (:-) where
  id = Sub Dict
  f . g = Sub $ Dict \\ f \\ g
  source _ = Dict
  target _ = Dict

lmap :: (Ob c, Contravariant f) => (a ~> b) -> f b c ~> f a c
lmap f = runNat (contramap f)

dimap :: (Profunctor (p :: i -> j -> k), Category (Hom :: i -> i -> *), Category (Hom :: j -> j -> *), Category (Hom :: k -> k -> *)) => (a ~> b) -> (c ~> d) -> p b c ~> p a d
dimap f g = case target g of
  Dict -> case target f of
    Dict -> runNat (contramap f) . fmap1 g

_Sub :: Iso (a :- b) (c :- d) (Dict a -> Dict b) (Dict c -> Dict d)
_Sub = dimap (\pq Dict -> case pq of Sub q -> q) (\f -> Sub $ f Dict)

newtype Magic a b c = Magic ((a |- b) => c)

_Implies :: Thin (Arr c) => Iso (Dict (a |- b)) (Dict (c |- d)) (a ~> b) (c ~> d)
_Implies = dimap (\Dict -> implies) (reify Dict) where
  reify :: forall a b c. ((a |- b) => c) -> (a ~> b) -> c
  reify k = unsafeCoerce (Magic k :: Magic a b c)

newtype Get (r :: i) (a :: i) (b :: i) = Get { runGet :: a ~> r }
_Get :: Iso (Get r a b) (Get s c d) (a ~> r) (c ~> s)
_Get = dimap runGet Get

instance Discrete Get
instance Category (Hom :: i -> i -> *) => Functor (Get :: i -> i -> i -> *) where fmap f = Nat $ Nat $ _Get (f .)
instance Discrete (Get r)
instance Category (Arr r) => Contravariant (Get r) where contramap f = Nat $ _Get (. f)
instance Discrete (Get r a)
instance Functor (Get r a) where fmap _ = Get . runGet
instance Contravariant (Get r a) where contramap _ = Get . runGet

get :: (Category (Arr a), Ob a) => (Get a a a -> Get a s s) -> s ~> a
get l = runGet $ l (Get id)

newtype Beget (r :: i) (a :: i) (b :: i) = Beget { runBeget :: r ~> b }
instance Discrete Beget
instance Category (Hom :: i -> i -> *) => Contravariant (Beget :: i -> i -> i -> *) where contramap f = Nat $ Nat $ _Beget (. f)
instance Discrete (Beget r)
instance Functor (Beget r) where fmap _ = Nat $ Beget . runBeget
instance Contravariant (Beget r) where contramap _ = Nat $ Beget . runBeget
instance Discrete (Beget r a)
instance Category (Hom :: i -> i -> *) => Functor (Beget r a :: i -> *) where fmap f = _Beget (f .)

_Beget :: Iso (Beget r a b) (Beget s c d) (r ~> b) (s ~> d)
_Beget = dimap runBeget Beget

beget :: (Category (Arr b), Ob b) => (Beget b b b -> Beget b t t) -> b ~> t
beget l = runBeget $ l (Beget id)

instance Thin (Hom :: i -> i -> *) => Contravariant ((|-) :: i -> i -> Constraint) where
  contramap f = Nat $ beget _Sub $ _Implies (. f)

instance Thin (Hom :: i -> i -> *) => Functor ((|-) p :: i -> Constraint) where
  fmap f = beget _Sub $ _Implies (f .)

instance Discrete (Ob :: i -> Constraint) => Functor (LimC :: (i -> Constraint) -> Constraint) where
  fmap f = ins . both (fmap1 f) (fmap f) . cls where
   both :: (a :- b) -> (c :- d) -> (a & c) :- (b & d)
   both g h = Sub $ Dict \\ g \\ h

instance Functor (Compose :: (j -> Constraint) -> (i -> j) -> (i -> Constraint)) where
  fmap (Nat f) = nat $ \(Proxy :: Proxy f) -> nat $ \(Proxy :: Proxy a) -> _Compose $
    case ob :: Ob a :- Ob (f a) of
      Sub Dict -> f

{-
class Category hom => Composed (hom :: k -> k -> *) where
  type Compose :: (j -> k) -> (i -> j) -> i -> k
  compose :: f (g a) `hom` Compose f g a
  decompose :: Compose f g a `hom` f (g a)
-}

{-
instance Composed (->) where
  type Compose = Compose1
  compose = Compose
  decompose = getCompose
-}

--instance Composed (:-) where
--  compose = Sub Dict
--  decompose = Sub Dict

--_Compose :: Composed (Hom :: k -> k -> *) => Iso (Compose (f :: j -> k) g a) (Compose (h :: j -> k) i b) (f (g a)) (h (i b))
--_Compose = dimap decompose compose

-- * Constraints

data CONST = Const
type Const = (Any 'Const :: j -> i -> j)

class a => ConstC a b
instance a => ConstC a b

instance Class a (Const a b) where cls = get _Const
instance a :=> Const a b where ins = beget _Const

class hom ~ Hom => Complete (hom :: j -> j -> *) where
  type Lim :: (i -> j) -> j
  elim :: Ob a => hom (Lim g) (g a)

  _Const :: (Ob a, Ob b, Ob c, Ob d) => Iso (Const a b) (Const c d) (a :: j) (c :: j)
  complete :: Category (Hom :: i -> i -> *) => Dict (Const -| (Lim :: (i -> j) -> j))
  obConst1 :: Ob (a :: j) :- Ob (Const a)
  obConst2 :: Ob b :- Ob (Const a b :: j)

instance Functor ConstC where
  fmap f = Nat $ Sub $ Dict \\ f

instance Complete (hom :: j -> j -> *) => Discrete (Const :: j -> i -> j) where
  ob = obConst1

instance Complete (hom :: j -> j -> *) => Discrete (Const a :: i -> j) where
  ob = obConst2

instance Complete (hom :: j -> j -> *) => Functor (Const :: j -> i -> j) where
  fmap = _Const

instance Complete (hom :: j -> j -> *) => Functor (Const a :: i -> j) where
  fmap _ = _Const id

instance Complete (hom :: j -> j -> *) => Contravariant (Const a :: i -> j) where
  contramap _ = _Const id

instance Category (Hom :: i -> i -> *) => (ConstC :: Constraint -> i -> Constraint) -| (LimC :: (i -> Constraint) -> Constraint) where
  adj = dimap todo todo
  {-
  adj = dimap hither yon where
    hither :: Ob f => Nat (ConstC a) (f :: i -> Constraint) -> a :- LimC f
    hither (Nat f) = Sub $ fmap ins $ _ -- beget _Implies $ Nat $ Sub $ fmap f Dict
    yon :: forall f a. Ob f => (a :- LimC f) -> Nat (ConstC a) (f :: i -> Constraint)
    yon f = Nat $ Sub $ case f of Sub Dict -> _ -- case ob :: Ob a :- Ob (f a) of Sub Dict -> Dict
  -}

instance Complete (:-) where
  type Lim = LimC
  elim = elim' where
    elim' :: forall g (a :: i). Ob a => LimC g ~> g a
    elim' = sub $ \(Proxy :: Proxy (LimC g)) -> case cls :: LimC g :- ((Ob |- g) & Discrete g) of
      Sub Dict -> case implies :: Ob ~> g of
        Nat w -> fmap w Dict
  complete = Dict


instance Discrete Lim1
instance Functor Lim1 where
  fmap (Nat f) (Lim a) = Lim (f a)
instance Const -| Lim1 where
  adj = dimap (\f a -> Lim (runNat f (beget _Const a))) $ \h -> Nat $ getLim . h . get _Const

instance Complete (->) where
  type Lim = Lim1
  elim = getLim
  complete = Dict

newtype Lim1 (p :: i -> *) = Lim { getLim :: forall a. Ob a => p a }

instance Category (Hom :: j -> j -> *) => Contravariant (Nat :: (i -> j) -> (i -> j) -> *) where contramap f = Nat (. f)
instance Category (Hom :: j -> j -> *) => Functor (Nat f :: (i -> j) -> *) where fmap = (.)
instance Category (Hom :: j -> j -> *) => Category (Nat :: (i -> j) -> (i -> j) -> *) where
  id = Nat id1 where
    id1 :: forall hom f x. (Category (hom :: j -> j -> *), Discrete f, Ob x) => hom (f x) (f x)
    id1 = id \\ (ob :: Ob x :- Ob (f x))
  source Nat{} = Dict
  target Nat{} = Dict
  Nat f . Nat g = Nat (f . g)


class (Functor p, Post Functor p) => Bifunctor p
instance (Functor p, Post Functor p) => Bifunctor p

class (Functor f, Functor u, Category (Hom :: i -> i -> *), Category (Hom :: j -> j -> *)) => (f :: j -> i) -| (u :: i -> j) | f -> u, u -> f where
  adj :: (Ob (a :: j), Ob (b :: i), Ob (c :: j), Ob (d :: i)) => Iso (f a ~> b) (f c ~> d) (a ~> u b) (c ~> u d)
  -- adj :: Iso' (Up f) (Down u)

class Curried p q | p -> q, q -> p where
  curried :: (Ob a, Ob b, Ob c, Ob d, Ob e, Ob f) => Iso (p a b ~> c) (p d e ~> f) (a ~> q b c) (d ~> q e f)

-}
-}
