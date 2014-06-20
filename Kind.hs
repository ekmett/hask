{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
module Kind where

import Data.Tagged
import Data.Proxy
import Data.Void
import qualified Data.Monoid as Monoid
import Data.Functor.Identity
import qualified Control.Applicative as Applicative
import qualified Data.Functor.Contravariant as Contravariant
import Control.Category (Category(..))
import qualified Control.Arrow as Arrow
import qualified Prelude
import Prelude (Either(..), ($), either)

-- * A kind-indexed family of categories

infixr 0 ~>
type family (~>) :: i -> i -> *
type instance (~>) = (->)
type instance (~>) = Nat

-- * Natural transformations form a category, using parametricity as a proxy for naturality

newtype Nat f g = Nat { runNat :: forall a. f a ~> g a }

instance Category ((~>) :: j -> j -> *) => Category (Nat :: (i -> j) -> (i -> j) -> *) where
  id = Nat id
  Nat f . Nat g = Nat (f . g)

-- * Functors between these kind-indexed categories

class Functor (f :: x -> y) where
  fmap :: (a ~> b) -> f a ~> f b

class Contravariant (f :: x -> y) where
  contramap :: (b ~> a) -> f a ~> f b

class PFunctor (p :: x -> y -> z) where
  first :: (a ~> b) -> p a c ~> p b c

class QFunctor (p :: x -> y -> z) where
  second :: (a ~> b) -> p c a ~> p c b

class PContravariant (p :: x -> y -> z) where
  lmap :: (a ~> b) -> p b c ~> p a c

class QContravariant (p :: x -> y -> z) where
  qmap :: (a ~> b) -> p c b ~> p c a

-- Lift Prelude instances of Functor without overlap
instance Prelude.Functor f => Functor f where
  fmap = Prelude.fmap

instance Contravariant.Contravariant f => Contravariant f where
  contramap = Contravariant.contramap

instance Category ((~>) :: j -> j -> *) => Functor (Nat f :: (i -> j) -> *) where
  fmap = (.)

-- We can defne a functor from the category of natural transformations to Hask
newtype At (x :: i) (f :: i -> *) = At { getAt :: f x }
_At = dimap getAt At

instance Functor (At x) where
  fmap (Nat f) = _At f

-- type family K (b :: *) :: i
-- type instance K b = b
-- type instance K b = Const b

-- .. and back
newtype Const (b :: *) (a :: i) = Const { getConst :: b }
_Const = dimap getConst Const

instance Functor Const where
  fmap f = Nat (_Const f)

-- * Support for Tagged and Proxy

_Tagged = dimap unTagged Tagged

instance Functor Proxy where
  fmap _ Proxy = Proxy

newtype Lift (p :: j -> k -> *) (f :: i -> j) (g :: i -> k) (a :: i) = Lift { lower :: p (f a) (g a) }
_Lift = dimap lower Lift

instance PFunctor (,) where
  first = Arrow.first

instance PFunctor Either where
  first = Arrow.left

instance PFunctor p => PFunctor (Lift p) where
  first (Nat f) = Nat (_Lift $ first f)

instance PFunctor Tagged where
  first _ = _Tagged id

instance Category ((~>) :: x -> x -> *) => QFunctor (Hom :: x -> x -> *) where
  second g (Hom h) = Hom (g . h)

instance QFunctor (->) where
  second = (.)

instance QFunctor ((~>) :: j -> j -> *) => QFunctor (Nat :: (i -> j) -> (i -> j) -> *) where
  second (Nat ab) (Nat ca) = Nat (second ab ca)

instance QFunctor (,) where
  second = Arrow.second

instance QFunctor Either where
  second = Arrow.right

instance QFunctor (Const :: * -> i -> *) where
  second _ = _Const id

instance QFunctor p => QFunctor (Lift p) where
  second (Nat f) = Nat (_Lift $ second f)

instance QFunctor At where
  second (Nat f) = _At f

instance QFunctor Tagged where
  second = Prelude.fmap

newtype Hom a b = Hom { runHom :: a ~> b }
_Hom = dimap runHom Hom

instance PContravariant (->) where
  lmap f g = g . f

instance Category ((~>) :: x -> x -> *) => PContravariant (Hom :: x -> x -> *) where
  lmap f = _Hom (.f)

instance PContravariant ((~>)::j->j-> *) => PContravariant (Nat::(i->j)->(i->j)-> *) where
  lmap (Nat ab) (Nat bc) = Nat (lmap ab bc)

instance PContravariant p => PContravariant (Lift p) where
  lmap (Nat f) = Nat $ _Lift (lmap f)

instance PContravariant Tagged where
  lmap _ = _Tagged id

instance QContravariant (Const :: * -> i -> *) where
  qmap _ = _Const id

instance QContravariant p => QContravariant (Lift p) where
  qmap (Nat f) = Nat $ _Lift (qmap f)

instance Contravariant (Const k :: i -> *) where
  contramap _ = _Const id

class (PFunctor p, QFunctor p, Category ((~>)::z->z-> *)) => Bifunctor (p :: x -> y -> z)
instance (PFunctor p, QFunctor p, Category ((~>)::z->z -> *)) => Bifunctor (p :: x -> y -> z)

type Ungetter t b = forall p. Bifunctor p => p b b -> p t t

unto :: (b ~> t) -> Ungetter t b
unto f = bimap f f

class (PContravariant p, QFunctor p, Category ((~>)::z->z-> *)) => Profunctor (p::x->y->z)
instance (PContravariant p, QFunctor p, Category ((~>)::z->z-> *)) => Profunctor (p::x->y->z)

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

class (PContravariant p, QContravariant p, Category ((~>)::z->z-> *)) => Bicontravariant (p::x->y->z)
instance (PContravariant p, QContravariant p, Category ((~>)::z->z-> *)) => Bicontravariant (p::x->y->z)

bicontramap :: Bicontravariant p => (a ~> b) -> (c ~> d) -> p b d ~> p a c
bicontramap f g = lmap f . qmap g

type Getter s a = forall p. Bicontravariant p => p a a -> p s s

to :: (s ~> a) -> Getter s a
to f = bicontramap f f

newtype Get r a b = Get { runGet :: a ~> r }
_Get = dimap runGet Get

instance Category ((~>)::i->i-> *) => PContravariant (Get (r :: i)) where
  lmap f = _Get (. f)

instance QContravariant (Get r) where
  qmap _ = _Get id

instance QFunctor (Get r) where
  second _ = _Get id

get :: forall (s::i) (a::i). Category ((~>)::i->i-> *) => (Get a a a -> Get a s s) -> s ~> a
get l = runGet $ l (Get id)

unget :: forall (t::i) (b::i). Category ((~>)::i->i-> *) => (Unget b b b -> Unget b t t) -> b ~> t
unget l = runUnget $ l (Unget id)

newtype Unget r a b = Unget { runUnget :: r ~> b }
_Unget = dimap runUnget Unget

newtype Un (p::i->i->j) (a::i) (b::i) (s::i) (t::i) = Un { runUn :: p t s ~> p b a }
_Un = dimap runUn Un

instance (Category ((~>)::j->j-> *), QFunctor p) => PContravariant (Un (p::i->i->j) a b) where
  lmap f = _Un $ dimap Hom runHom $ lmap (second f)

instance (Category ((~>)::j->j-> *), QContravariant p) => PFunctor (Un (p::i->i->j) a b) where
  first f = _Un $ dimap Hom runHom $ lmap (qmap f)

instance (Category ((~>)::j->j-> *), PContravariant p) => QFunctor (Un (p::i->i->j) a b) where
  second g = _Un $ dimap Hom runHom $ lmap (lmap g)

instance (Category ((~>)::j->j-> *), PFunctor p) => QContravariant (Un (p::i->i->j) a b) where
  qmap f = _Un $ dimap Hom runHom $ lmap (first f)

un :: (Un p a b a b -> Un p a b s t) -> p t s -> p b a
un l = runUn $ l (Un id)

instance PFunctor (Unget r) where first _ = _Unget id
instance PContravariant (Unget r) where lmap _ = _Unget id
instance Category ((~>) :: i -> i -> *) => QFunctor (Unget (r :: i)) where second f = _Unget (f .)

class (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)
instance (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)

class (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)
instance (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)

rmap :: QFunctor p => (a ~> b) -> p c a ~> p c b
rmap = second

bimap :: (Category ((~>) :: z -> z -> *), Bifunctor (p :: x -> y -> z)) => (a ~> b) -> (c ~> d) -> p a c ~> p b d
bimap f g = first f . second g

dimap :: (Category ((~>) :: z -> z -> *), Profunctor (p :: x -> y -> z)) => (a ~> b) -> (c ~> d) -> p b c ~> p a d
dimap f g = lmap f . rmap g


-- tensor for a skew monoidal category
class Bifunctor p => Tensor (p :: x -> x -> x) where
  type Id p :: x
  associate :: p (p a b) c ~> p a (p b c)
  lambda    :: p (Id p) a ~>  a
  rho       :: a ~> p a (Id p)

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
  swap :: p a b ~> p b a

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

lambdaProf :: forall (p :: i -> j -> *) (a :: i) (b :: j). QFunctor p => Prof (~>) p a b -> p a b
lambdaProf (Prof h p) = rmap h p

rhoProf :: forall (p :: i -> k -> *) (a :: i) (b :: k). Category ((~>) :: i -> i -> *) => p a b -> Prof p (~>) a b
rhoProf p = Prof p id

class One ~ t => Terminal (t :: i) | i -> t where
  type One :: i
  terminal :: a ~> t

instance Terminal () where
  type One = ()
  terminal _ = ()

-- we can only offer the terminal object for Nat :: (i -> *), not Nat :: (i -> j)
instance Terminal (Const ()) where
  type One = Const ()
  terminal = Nat (Const . terminal)

class Zero ~ t => Initial (t :: i) | i -> t where
  type Zero :: i
  initial :: t ~> a

instance Initial Void where
  type Zero = Void
  initial = absurd

-- we can only offer the initial object for Nat :: (i -> *), not Nat :: (i -> j)
instance Initial (Const Void) where
  type Zero = Const Void
  initial = Nat $ initial . getConst

infixl 7 *
class (h ~ (~>), Symmetric ((*)::i->i->i), Tensor ((*)::i->i->i), Terminal (Id ((*)::i->i->i))) => Cartesian (h :: i -> i -> *) | i -> h where
  type (*) :: i -> i -> i
  fst   :: forall (a::i) (b::i). a * b ~> a
  snd   :: forall (a::i) (b::i). a * b ~> b
  (&&&) :: forall (a::i) (b::i) (c::i). (a ~> b) -> (a ~> c) -> a ~> b * c

instance Cartesian (->) where
  type (*) = (,)
  fst   = Prelude.fst
  snd   = Prelude.snd
  (&&&) = (Arrow.&&&)

instance Cartesian (Nat :: (i -> *) -> (i -> *) -> *) where
  type (*) = Lift (,)
  fst = Nat $ fst . lower
  snd = Nat $ snd . lower
  Nat f &&& Nat g = Nat $ Lift . (f &&& g)

class (Cartesian ((~>) :: i -> i -> *), Profunctor p) => Strong (p :: i -> i -> *) where
  {-# MINIMAL _1 | _2 #-}
  _1 :: p a b -> p (a * c) (b * c)
  _1 = dimap swap swap . _2
  _2 :: p a b -> p (c * a) (c * b)
  _2 = dimap swap swap . _1

instance Strong (->) where
  _1 = first
  _2 = second

instance Strong (Nat::(i-> *)->(i-> *)-> *) where
  _1 = first
  _2 = second

instance Cartesian ((~>)::i->i-> *) => Strong (Get (r::i)) where
  _1 = _Get (. fst)

type Lens s t a b = forall p. Strong p => p a b -> p s t

infixl 6 +
class (h ~ (~>), Symmetric ((+)::i->i->i), Tensor ((+)::i->i->i),Initial (Id ((+)::i->i->i))) => Cocartesian (h :: i -> i -> *) | i -> h where
  type (+) :: i -> i -> i
  inl    :: forall (a :: i) (b :: i). a ~> a + b
  inr    :: forall (a :: i) (b :: i). b ~> a + b
  (|||)  :: forall (a :: i) (b :: i) (c :: i). (a ~> c) -> (b ~> c) -> a + b ~> c

instance Cocartesian (->) where
  type (+) = Either
  inl = Left
  inr = Right
  (|||) = either

instance Cocartesian (Nat :: (i -> *) -> (i -> *) -> *) where
  type (+) = Lift Either
  inl = Nat (Lift . Left)
  inr = Nat (Lift . Right)
  Nat f ||| Nat g = Nat $ either f g . lower

class (Cocartesian ((~>) :: i -> i -> *), Profunctor p) => Choice (p :: i -> i -> *) where
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

instance Choice Tagged where
  _Left  = bimap inl inl
  _Right = bimap inr inr

instance Cocartesian ((~>) :: i -> i -> *) => Choice (Unget (r :: i)) where
  _Left = bimap inl inl
  _Right = bimap inr inr

type Prism s t a b = forall p. Choice p => p a b -> p s t

type a ^ b = Exp b a
infixr 8 ^

class (Profunctor (Exp :: x -> x -> x), Cartesian k) => CCC (k :: x -> x -> *) | x -> k where
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

type (f :: y -> x) -: (u :: x -> y) = forall a b a' b'. Iso (f a ~> b) (f a' ~> b') (a ~> u b) (a' ~> u b')

class (Functor f, Functor u, Category ((~>) :: x -> x -> *), Category ((~>) :: y -> y -> *)) => (f :: y -> x) -| (u :: x -> y) | f -> u, u -> f where
  adj :: f -: u

cccAdj :: forall (e :: i). CCC ((~>) :: i -> i -> *) => (*) e -: Exp e
cccAdj = dimap (. swap) (. swap) . curried

unitAdj :: (f -| u) => a ~> u (f a)
unitAdj = get adj id

counitAdj :: (f -| u) => f (u b) ~> b
counitAdj = unget adj id

class (Cartesian ((~>) :: x -> x -> *), Cartesian ((~>) :: y -> y -> *), Functor f) => Monoidal (f :: x -> y) where
  ap1 :: One ~> f One
  ap2 :: f a * f b ~> f (a * b)

class (Cocartesian ((~>) :: x -> x -> *), Cocartesian ((~>) :: y -> y -> *), Functor f) => Opmonoidal (f :: x -> y) where
  op1 :: f Zero ~> Zero
  op2 :: f (a + b) ~> f a + f b

-- lift applicatives for Hask
instance Applicative.Applicative f => Monoidal f where
  ap1 = Applicative.pure
  ap2 = uncurry $ Applicative.liftA2 (,)

instance Opmonoidal Identity where
  op1 = runIdentity
  op2 = bimap Identity Identity . runIdentity

-- a monoid object in a cartesian category
class Cartesian ((~>) :: i -> i -> *) => Monoid (m :: i) where
  one  :: One ~> m
  mult :: m * m ~> m

instance Monoid.Monoid m => Monoid m where
  one () = Monoid.mempty
  mult = uncurry Monoid.mappend

class Functor f => Strength (f :: x -> y) where

ap :: forall (f :: x -> y) (a :: x) (b :: x).
      (Monoidal f, CCC ((~>) :: x -> x -> *), CCC ((~>) :: y -> y -> *))
   => f (b ^ a) ~> f b ^ f a
ap = curry (fmap apply . ap2)

-- point :: forall (f :: x -> x) (a :: x). Monoidal f, CCC ((~>) :: x -> x -> *)
--      => a ~> f a
