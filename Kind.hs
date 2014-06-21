{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
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
import Data.Functor.Identity
import qualified Data.Monoid as Monoid
import Data.Proxy
import Data.Tagged
import qualified Data.Traversable as Traversable
import Data.Void
import qualified Prelude
import Prelude (Either(..), ($), either, Bool)
import GHC.Exts (Constraint, Any)
import Unsafe.Coerce (unsafeCoerce)

-- * A kind-indexed family of categories

infixr 0 ~>
type family (~>) :: i -> i -> *
type instance (~>) = (->) -- * -> * -> *
type instance (~>) = Nat  -- (i -> j) -> (i -> j) -> *
type instance (~>) = (:-) -- Constraint -> Constraint -> *
type instance (~>) = Prod -- (i,j) -> (i, j) -> *

data Prod :: (i,j) -> (i,j) -> * where
  Want :: Prod a a
  Have :: forall (a :: i) (b :: i) (c :: j) (d :: j). (a ~> b) -> (c ~> d) -> Prod '(a,c) '(b,d)

instance (Category ((~>) :: i -> i -> *), Category ((~>) :: j -> j -> *)) => Category (Prod :: (i,j) -> (i,j) -> *) where
  id = Want
  Want . f = f
  f . Want = f
  Have f f' . Have g g' = Have (f . g) (f' . g')

runProd :: forall (a :: i) (b :: i) (c :: j) (d :: j). (Category ((~>) :: i -> i -> *), Category ((~>) :: j -> j -> *)) => Prod '(a,c) '(b,d) -> (a ~> b, c ~> d)
runProd Want       = (id,id)
runProd (Have f g) = (f,g)

runFst :: forall (a :: i) (b :: i) (c :: j) (d :: j). Category ((~>) :: i -> i -> *) => Prod '(a,c) '(b,d) -> a ~> b
runFst Want       = id
runFst (Have f _) = f

runSnd :: forall (a :: i) (b :: i) (c :: j) (d :: j). Category ((~>) :: j -> j -> *) => Prod '(a,c) '(b,d) -> c ~> d
runSnd Want       = id
runSnd (Have _ g) = g

-- needed because we can't partially apply (,) in the world of constraints
class (p, q) => p & q
instance (p, q) => p & q

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

-- * common aliases
--
class (PFunctor p, QFunctor p, Category ((~>)::z->z-> *)) => Bifunctor (p :: x -> y -> z)
instance (PFunctor p, QFunctor p, Category ((~>)::z->z -> *)) => Bifunctor (p :: x -> y -> z)

class (PContravariant p, QContravariant p, Category ((~>)::z->z-> *)) => Bicontravariant (p::x->y->z)
instance (PContravariant p, QContravariant p, Category ((~>)::z->z-> *)) => Bicontravariant (p::x->y->z)

-- enriched profuncors C^op * D -> E
class (PContravariant p, QFunctor p, Cartesian ((~>)::z->z-> *)) => Profunctor (p::x->y->z)
instance (PContravariant p, QFunctor p, Cartesian ((~>)::z->z-> *)) => Profunctor (p::x->y->z)

-- Lift Prelude instances of Functor without overlap, using the kind index to say
-- these are all the instances of kind * -> *
instance Prelude.Functor f => Functor f where
  fmap = Prelude.fmap

instance Contravariant.Contravariant f => Contravariant f where
  contramap = Contravariant.contramap

instance (Category ((~>) :: i -> i -> *), Category ((~>) :: j -> j -> *)) => Functor (Prod p :: (i, j) -> *) where
  fmap = (.)

instance Category ((~>) :: j -> j -> *) => Functor (Nat f :: (i -> j) -> *) where
  fmap = (.)

instance Functor ((:-) f) where
  fmap = second

-- We can defne a functor from the category of natural transformations to Hask
newtype At (x :: i) (f :: i -> *) = At { getAt :: f x }
_At = dimap getAt At

instance Functor (At x) where
  fmap (Nat f) = _At f

-- .. and back
class Const ~ k => Constant (k :: j -> i -> j) | j i -> k where
  type Const :: j -> i -> j
  _Const :: forall (a :: i) (b :: j) (a' :: i) (b' :: j). Iso (Const b a) (Const b' a') b b'

newtype ConstValue (b :: *) (a :: i) = Const { getConst :: b }

instance Constant ConstValue where
  type Const = ConstValue
  _Const = dimap getConst Const

newtype ConstValue2 (f :: j -> *) (a :: i) (c :: j) = Const2 { getConst2 :: f c }
instance Constant ConstValue2 where
  type Const = ConstValue2
  _Const = dimap (Nat getConst2) (Nat Const2)

instance Constant ConstConstraint where
  type Const = ConstConstraint
  _Const = dimap (Sub Dict) (Sub Dict)

class b => ConstConstraint b a
instance b => ConstConstraint b a

instance Functor ConstValue where
  fmap f = Nat (_Const f)

instance Functor (ConstValue b) where
  fmap _ = _Const id

instance Functor ConstValue2 where
  fmap f = Nat (_Const f)

instance Functor (ConstValue2 f) where
  fmap _ = Nat $ Const2 . getConst2

instance Functor f => Functor (ConstValue2 f a) where
  fmap f = Const2 . fmap f . getConst2

instance Functor ConstConstraint where
  fmap f = Nat (_Const f)

instance Functor (ConstConstraint b) where
  fmap _ = Sub Dict

-- * -^J -| Limit

class (Limit ~ l, Constant (Const :: j -> i -> j)) => Limited (l :: (i -> j) -> j) | i j -> l where
  type Limit :: (i -> j) -> j
  _Limit :: forall (a :: j) (b :: j) (f :: i -> j) (g :: i -> j).
    Iso (Const a ~> f) (Const b ~> g) (a ~> Limit f) (b ~> Limit g)

newtype LimitValue (f :: i -> *) = Limit { getLimit :: forall x. f x }

instance Limited LimitValue where
  type Limit = LimitValue
  _Limit = dimap (\f a -> Limit (runNat f (Const a))) $ \h -> Nat $ getLimit . h . getConst

instance Functor LimitValue where
  fmap (Nat f) (Limit g) = Limit (f g)

newtype LimitValue2 (f :: i -> j -> *) (y :: j) = Limit2 { getLimit2 :: forall x. f x y }

instance Limited LimitValue2 where
  type Limit = LimitValue2
  _Limit = dimap (\(Nat f) -> Nat $ \ a -> Limit2 (runNat f (Const2 a))) $ \(Nat h) -> Nat $ Nat $ getLimit2 . h . getConst2

instance Functor LimitValue2 where
  fmap f = Nat $ \(Limit2 g) -> Limit2 (runNat (runNat f) g)

-- has to abuse Any because any inhabits every kind, but it is not a good choice of Skolem!
class LimitConstraint (p :: i -> Constraint) where
  limitDict :: Dict (p a)

instance p Any => LimitConstraint (p :: i -> Constraint) where
  limitDict = case unsafeCoerce (id :: p Any :- p Any) :: p Any :- p a of
    Sub d -> d

instance Limited LimitConstraint where
  type Limit = LimitConstraint
  _Limit = dimap (hither . runNat) (\b -> Nat $ dimap (Sub Dict) (Sub limitDict) b) where
    hither :: (ConstConstraint a Any :- f Any) -> a :- LimitConstraint f
    hither = dimap (Sub Dict) (Sub Dict)

-- * Colimit -| -^J

class (Colimit ~ l, Constant (Const :: j -> i -> j)) => Colimited (l :: (i -> j) -> j) | i j -> l where
  type Colimit :: (i -> j) -> j
  _Colimit :: forall (a :: j) (b :: j) (f :: i -> j) (g :: i -> j).
    Iso (Colimit f ~> a) (Colimit g ~> b) (f ~> Const a) (g ~> Const b)

data ColimitValue (f :: i -> *) where
  Colimit :: f x -> ColimitValue f

instance Colimited ColimitValue where
  type Colimit = ColimitValue
  _Colimit = dimap (\f -> Nat $ Const . f . Colimit) $ \(Nat g2cb) (Colimit g) -> getConst (g2cb g)

instance Functor ColimitValue where
  fmap (Nat f) (Colimit g)= Colimit (f g)

data ColimitValue2 (f :: i -> j -> *) (x :: j) where
  Colimit2 :: f y x -> ColimitValue2 f x

instance Colimited ColimitValue2 where
  type Colimit = ColimitValue2
  _Colimit = dimap (\(Nat f) -> Nat $ Nat $ Const2 . f . Colimit2) $
                    \ f -> Nat $ \ xs -> case xs of
                      Colimit2 fyx -> getConst2 $ runNat (runNat f) fyx

instance Functor ColimitValue2 where
  fmap f = Nat $ \(Colimit2 g) -> Colimit2 (runNat (runNat f) g)

-- * Support for Tagged and Proxy

_Tagged :: Iso (Tagged s a) (Tagged t b) a b
_Tagged = dimap unTagged Tagged

instance Monoidal (Tagged s) where
  ap1 = Tagged
  ap2 = Tagged . bimap unTagged unTagged

instance Opmonoidal (Tagged s) where
  op1 = unTagged
  op2 = bimap Tagged Tagged . unTagged

instance Functor Proxy where
  fmap _ Proxy = Proxy

instance Cartesian ((~>) :: i -> i -> *) => Monoidal (Proxy :: i -> *) where
  ap1 () = Proxy
  ap2 (Proxy, Proxy) = Proxy

-- * Dictionaries

-- Dict :: Constraint -> * switches categories from the category of constraints to Hask
instance Functor Dict where
  fmap p Dict = Dict \\ p

class Lift ~ s => Lifted (s :: (j -> k -> l) -> (i -> j) -> (i -> k) -> i -> l) | i j k l -> s where
  type Lift :: (j -> k -> l) -> (i -> j) -> (i -> k) -> i -> l
  _Lift :: forall (q :: j -> k -> l) (r :: j -> k -> l) (f :: i -> j) (g :: i -> k) (h :: i -> j) (e :: i -> k) (a :: i) (b :: i). Iso (Lift q f g a)  (Lift r h e b) (q (f a) (g a)) (r (h b) (e b))

newtype LiftValue (p :: j -> k -> *) (f :: i -> j) (g :: i -> k) (a :: i) = Lift { lower :: p (f a) (g a) }
instance Lifted LiftValue where
  type Lift = LiftValue
  _Lift = dimap lower Lift

instance (Bifunctor p, Functor f, Functor g) => Functor (LiftValue p f g) where
  fmap f = _Lift (bimap (fmap f) (fmap f))

instance PFunctor p => Functor (LiftValue p) where
  fmap f = Nat $ Nat $ _Lift $ first $ runNat f -- f = _Lift (bimap (fmap f) (fmap f))

instance Functor LiftValue where
  fmap f = Nat $ Nat $ Nat $ _Lift $ runNat (runNat f)

class r (p a) (q a) => LiftConstraint (r :: j -> k -> Constraint) (p :: i -> j) (q :: i -> k) (a :: i)

instance r (p a) (q a) => LiftConstraint r p q a

instance Lifted LiftConstraint where
  type Lift = LiftConstraint
  _Lift = dimap (Sub Dict) (Sub Dict)

newtype LiftValue2 (p :: (l -> j) -> (l -> k) -> l -> *) (f :: i -> l -> j) (g :: i -> l -> k) (a :: i) (b :: l) = Lift2 { lower2 :: p (f a) (g a) b }
instance Lifted LiftValue2 where
  type Lift = LiftValue2
  _Lift = dimap (Nat lower2) (Nat Lift2)

instance PFunctor (,) where
  first = Arrow.first

instance Functor (,) where
  fmap f = Nat (first f)

instance PFunctor (&) where
  first f = Sub $ Dict \\ f

instance Functor (&) where
  fmap f = Nat (first f)

instance PFunctor Either where
  first = Arrow.left

instance Functor Either where
  fmap f = Nat (first f)

instance QFunctor (:-) where
  second = dimap Hom runHom . second

instance Contravariant (:-) where
  contramap f = Nat $ lmap f

instance PContravariant (:-) where
  lmap = dimap Hom runHom . lmap

instance PFunctor p => PFunctor (LiftValue p) where
  first (Nat f) = Nat (_Lift $ first f)

instance PFunctor p => PFunctor (LiftValue2 p) where
  first (Nat f) = Nat (_Lift $ first f)

instance PFunctor p => PFunctor (LiftConstraint p) where
  first (Nat f) = Nat (_Lift $ first f)

instance PFunctor Tagged where
  first _ = _Tagged id

instance Functor Tagged where
  fmap f = Nat (first f)

instance (Category ((~>) :: i -> i -> *), Category ((~>) :: j -> j -> *)) => QFunctor (Prod :: (i, j) -> (i, j) -> *) where
  second = (.)

instance Category ((~>) :: x -> x -> *) => QFunctor (Hom :: x -> x -> *) where
  second g (Hom h) = Hom (g . h)

instance QFunctor (->) where
  second = (.)

instance QFunctor ((~>) :: j -> j -> *) => QFunctor (Nat :: (i -> j) -> (i -> j) -> *) where
  second (Nat ab) (Nat ca) = Nat (second ab ca)

instance QFunctor (&) where
  second p = Sub $ Dict \\ p

instance QFunctor (,) where
  second = Arrow.second

instance QFunctor Either where
  second = Arrow.right

instance QFunctor (ConstValue :: * -> i -> *) where
  second _ = _Const id

instance QFunctor (ConstValue2 :: (j -> *) -> i -> j -> *) where
  second _ = _Const id

instance QFunctor p => QFunctor (LiftValue p) where
  second (Nat f) = Nat (_Lift $ second f)

instance QFunctor p => Functor (LiftValue p e) where
  fmap (Nat f) = Nat (_Lift $ second f)

instance QFunctor p => QFunctor (LiftValue2 p) where
  second (Nat f) = Nat (_Lift $ second f)

instance QFunctor p => Functor (LiftValue2 p e) where
  fmap (Nat f) = Nat (_Lift $ second f)

instance QFunctor p => QFunctor (LiftConstraint p) where
  second (Nat f) = Nat (_Lift $ second f)

instance QFunctor p => Functor (LiftConstraint p e) where
  fmap (Nat f) = Nat (_Lift $ second f)

instance QFunctor At where
  second (Nat f) = _At f

instance QFunctor Tagged where
  second = Prelude.fmap

data Via (a :: x) (b :: x) (s :: x) (t :: x) where
  Via :: (s ~> a) -> (b ~> t) -> Via a b s t

-- TODO: variances for the other postions

instance PContravariant ((~>) :: x -> x -> *) => PContravariant (Via a b :: x -> x -> *) where
  lmap f (Via g h) = Via (lmap f g) h

instance PContravariant ((~>) :: x -> x -> *) => Contravariant (Via a b :: x -> x -> *) where
  contramap f = Nat (lmap f)

instance PFunctor ((~>) :: x -> x -> *) => PFunctor (Via a b :: x -> x -> *) where
  first f (Via g h) = Via (first f g) h

instance PFunctor ((~>) :: x -> x -> *) => Functor (Via a b :: x -> x -> *) where
  fmap f = Nat (first f)

instance QContravariant ((~>) :: x -> x -> *) => QContravariant (Via a b :: x -> x -> *) where
  qmap f (Via g h) = Via g (qmap f h)

instance QFunctor ((~>) :: x -> x -> *) => QFunctor (Via a b :: x -> x -> *) where
  second f (Via g h) = Via g (second f h)

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

mapping
   :: forall (f :: x -> y) (a :: x) (b :: x) (s :: x) (t :: x).
      (Category ((~>) :: x -> x -> *), Functor f)
   => (Via a b a b -> Via a b s t) -> Iso (f s) (f t) (f a) (f b)
mapping l = case l (Via id id) of
  Via csa dbt -> dimap (fmap csa) (fmap dbt)

newtype Hom a b = Hom { runHom :: a ~> b }
_Hom = dimap runHom Hom

instance PContravariant (->) where
  lmap f g = g . f

instance Contravariant (->) where
  contramap f = Nat (lmap f)

instance Category ((~>) :: x -> x -> *) => PContravariant (Hom :: x -> x -> *) where
  lmap f = _Hom (.f)

instance Category ((~>) :: x -> x -> *) => Contravariant (Hom :: x -> x -> *) where
  contramap f = Nat (lmap f)

instance (PContravariant ((~>) :: i -> i -> *), PContravariant ((~>) :: j -> j -> *)) => PContravariant (Prod :: (i, j) -> (i, j) -> *) where
  lmap (Have f f') (Have g g') = Have (lmap f g) (lmap f' g')
  lmap Want f = f
  lmap f Want = f
instance (PContravariant ((~>) :: i -> i -> *), PContravariant ((~>) :: j -> j -> *)) => Contravariant (Prod :: (i, j) -> (i, j) -> *) where
  contramap f = Nat (lmap f)

instance PContravariant ((~>)::j->j-> *) => PContravariant (Nat::(i->j)->(i->j)-> *) where
  lmap (Nat ab) (Nat bc) = Nat (lmap ab bc)

instance PContravariant ((~>)::j->j-> *) => Contravariant (Nat::(i->j)->(i->j)-> *) where
  contramap f = Nat (lmap f)

instance PContravariant p => PContravariant (LiftValue p) where
  lmap (Nat f) = Nat $ _Lift (lmap f)

instance PContravariant p => Contravariant (LiftValue p) where
  contramap f = Nat (lmap f)

instance PContravariant p => PContravariant (LiftValue2 p) where
  lmap (Nat f) = Nat $ _Lift (lmap f)

instance PContravariant p => Contravariant (LiftValue2 p) where
  contramap f = Nat (lmap f)

instance PContravariant p => PContravariant (LiftConstraint p) where
  lmap (Nat f) = Nat $ _Lift (lmap f)

instance PContravariant p => Contravariant (LiftConstraint p) where
  contramap f = Nat (lmap f)

instance PContravariant Tagged where
  lmap _ = _Tagged id

instance Contravariant Tagged where
  contramap f = Nat (lmap f)

instance QContravariant (ConstValue :: * -> i -> *) where
  qmap _ = _Const id

instance QContravariant (ConstValue2 :: (j -> *) -> i -> j -> *) where
  qmap _ = _Const id

instance QContravariant p => QContravariant (LiftValue p) where
  qmap (Nat f) = Nat $ _Lift (qmap f)

instance QContravariant p => QContravariant (LiftValue2 p) where
  qmap (Nat f) = Nat $ _Lift (qmap f)

instance QContravariant p => QContravariant (LiftConstraint p) where
  qmap (Nat f) = Nat $ _Lift (qmap f)

instance Contravariant (ConstValue k :: i -> *) where
  contramap _ = _Const id

instance Contravariant (ConstValue2 k :: i -> j -> *) where
  contramap _ = _Const id

type Ungetter t b = forall p. (Choice p, PFunctor p) => p b b -> p t t

unto :: (b ~> t) -> Ungetter t b
unto f = bimap f f

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

bicontramap :: Bicontravariant p => (a ~> b) -> (c ~> d) -> p b d ~> p a c
bicontramap f g = lmap f . qmap g

type Getter s a = forall p. (Strong p, QContravariant p) => p a a -> p s s

to :: (s ~> a) -> Getter s a
to f = bicontramap f f

newtype Get r a b = Get { runGet :: a ~> r }
_Get = dimap runGet Get

instance Category ((~>)::i->i-> *) => PContravariant (Get (r :: i)) where
  lmap f = _Get (. f)

instance Category ((~>)::i->i-> *) => Contravariant (Get (r :: i)) where
  contramap f = Nat (lmap f)

instance QContravariant (Get r) where
  qmap _ = _Get id

instance QFunctor (Get r) where
  second _ = _Get id

get :: forall (s::i) (a::i). Category ((~>)::i->i-> *) => (Get a a a -> Get a s s) -> s ~> a
get l = runGet $ l (Get id)
-- get = via _Get

-- * Unget

newtype Unget r a b = Unget { runUnget :: r ~> b }
_Unget = dimap runUnget Unget

instance PFunctor (Unget r) where
  first _ = _Unget id

instance PContravariant (Unget r) where
  lmap _ = _Unget id

instance Category ((~>) :: i -> i -> *) => QFunctor (Unget (r :: i)) where
  second f = _Unget (f .)

unget :: forall (t::i) (b::i). Category ((~>)::i->i-> *) => (Unget b b b -> Unget b t t) -> b ~> t
unget l = runUnget $ l (Unget id)
-- unget = via _Unget

(#) :: (Unget b b b -> Unget b t t) -> b -> t
(#) = unget

-- * Un

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
-- un = via _Un

class (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)
instance (PContravariant p, PFunctor p) => PPhantom (p :: x -> y -> z)

class (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)
instance (QContravariant p, QFunctor p) => QPhantom (p :: x -> y -> z)

rmap :: QFunctor p => (a ~> b) -> p c a ~> p c b
rmap = second

bimap :: (Category ((~>)::z->z-> *), Bifunctor (p::x->y->z)) => (a ~> b) -> (c ~> d) -> p a c ~> p b d
bimap f g = first f . second g

dimap :: (Category ((~>)::z->z-> *), Profunctor (p::x->y->z)) => (a ~> b) -> (c ~> d) -> p b c ~> p a d
dimap f g = lmap f . rmap g

-- tensor for a skew monoidal category
class Bifunctor p => Tensor (p :: x -> x -> x) where
  type Id p :: x
  associate :: p (p a b) c ~> p a (p b c)
  lambda    :: p (Id p) a ~> a
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

instance Tensor p => Tensor (LiftValue p) where
  type Id (LiftValue p) = ConstValue (Id p)
  associate = Nat $ _Lift $ second (unget _Lift) . associate . first (get _Lift)
  lambda    = Nat $ lmap (first (get _Const) . get _Lift) lambda
  rho       = Nat $ rmap (unget _Lift . second (unget _Const)) rho

instance Tensor p => Tensor (LiftValue2 p) where
  type Id (LiftValue2 p) = ConstValue2 (Id p)
  associate = Nat $ _Lift $ second (unget _Lift) . associate . first (get _Lift)
  lambda    = Nat $ lmap (first (get _Const) . get _Lift) lambda
  rho       = Nat $ rmap (unget _Lift . second (unget _Const)) rho

instance Tensor p => Tensor (LiftConstraint p) where
  type Id (LiftConstraint p) = ConstConstraint (Id p)
  associate = Nat $ _Lift $ second (unget _Lift) . associate . first (get _Lift)
  lambda    = Nat $ lmap (first (get _Const) . get _Lift) lambda
  rho       = Nat $ rmap (unget _Lift . second (unget _Const)) rho

instance Tensor (&) where
  type Id (&) = (() :: Constraint)
  associate = Sub Dict
  lambda = Sub Dict
  rho = Sub Dict

-- symmetric monoidal category
class Bifunctor p => Symmetric p where
  swap :: p a b ~> p b a

instance Symmetric (,) where
  swap (a,b) = (b, a)

instance Symmetric (&) where
  swap = Sub Dict

instance Symmetric Either where
  swap = either Right Left

instance Symmetric p => Symmetric (LiftValue p) where
  swap = Nat $ _Lift swap

instance Symmetric p => Symmetric (LiftValue2 p) where
  swap = Nat $ _Lift swap

instance Symmetric p => Symmetric (LiftConstraint p) where
  swap = Nat $ _Lift swap

-- profunctor composition forms a weak category.
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
instance Terminal (ConstValue ()) where
  type One = ConstValue ()
  terminal = Nat (Const . terminal)

instance Terminal (() :: Constraint) where
  type One = (() :: Constraint)
  terminal = Constraint.top

instance Terminal (ConstConstraint ()) where
  type One = ConstConstraint ()
  terminal = Nat (unget _Const . terminal)

class Zero ~ t => Initial (t :: i) | i -> t where
  type Zero :: i
  initial :: t ~> a

instance Initial Void where
  type Zero = Void
  initial = absurd

-- we can only offer the initial object for Nat :: (i -> *), not Nat :: (i -> j)
instance Initial (ConstValue Void) where
  type Zero = ConstValue Void
  initial = Nat $ initial . getConst

instance Initial (() ~ Bool) where
  type Zero = () ~ Bool
  initial = Constraint.bottom

instance Initial (ConstConstraint (() ~ Bool)) where
  type Zero = ConstConstraint (() ~ Bool)
  initial = Nat $ initial . get _Const

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

instance Cartesian (:-) where
  type (*) = (&)
  fst = Sub Dict
  snd = Sub Dict
  p &&& q = Sub $ Dict \\ p \\ q

instance Cartesian (Nat :: (i -> *) -> (i -> *) -> *) where
  type (*) = Lift (,)
  fst = Nat $ fst . lower
  snd = Nat $ snd . lower
  Nat f &&& Nat g = Nat $ Lift . (f &&& g)

instance Cartesian (Nat :: (i -> Constraint) -> (i -> Constraint) -> *) where
  type (*) = LiftConstraint (&)
  fst = Nat $ fst . get _Lift
  snd = Nat $ snd . get _Lift
  Nat f &&& Nat g = Nat $ unget _Lift . (f &&& g)

class (Cartesian ((~>) :: i -> i -> *), Profunctor p) => Strong (p :: i -> i -> *) where
  {-# MINIMAL _1 | _2 #-}
  _1 :: p a b -> p (a * c) (b * c)
  _1 = dimap swap swap . _2
  _2 :: p a b -> p (c * a) (c * b)
  _2 = dimap swap swap . _1

instance Strong (->) where
  _1 = first
  _2 = second

instance Strong (:-) where
  _1 = first
  _2 = second

instance Strong (Nat::(i-> *)->(i-> *)-> *) where
  _1 = first
  _2 = second

instance Strong (Nat::(i-> Constraint)->(i-> Constraint)-> *) where
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

-- | the isomorphism that witnesses f -| u
type (f :: y -> x) -: (u :: x -> y) = forall a b a' b'. Iso (f a ~> b) (f a' ~> b') (a ~> u b) (a' ~> u b')

-- |
-- @f -| u@ indicates f is left adjoint to u
class (Functor f, Functor u, Category ((~>) :: x -> x -> *), Category ((~>) :: y -> y -> *))
   => (f::y->x) -| (u::x->y) | f -> u, u -> f where
  adj :: f -: u

cccAdj :: forall (e :: i). CCC ((~>) :: i -> i -> *) => (*) e -: Exp e
cccAdj = dimap (. swap) (. swap) . curried

unitAdj :: (f -| u) => a ~> u (f a)
unitAdj = get adj id

counitAdj :: (f -| u) => f (u b) ~> b
counitAdj = unget adj id

instance (,) e -| (->) e where
  adj = cccAdj

instance LiftValue (,) e -| LiftValue (->) e where
  adj = cccAdj

-- instance LiftValue2 (LiftValue (,)) e -| LiftValue2 (LiftValue (->)) e where
--   adj = cccAdj

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

class (Cartesian ((~>) :: x -> x -> *), Cartesian ((~>) :: y -> y -> *), Functor f) => Monoidal (f :: x -> y) where
  ap1 :: One ~> f One
  ap2 :: f a * f b ~> f (a * b)

instance Monoidal Dict where
  ap1 () = Dict
  ap2 (Dict, Dict) = Dict

-- lift applicatives for Hask
instance Applicative.Applicative f => Monoidal f where
  ap1 = Applicative.pure
  ap2 = uncurry $ Applicative.liftA2 (,)

instance Monoidal ((:-) f) where
  ap1 () = terminal
  ap2 = uncurry (&&&)

instance Monoidal (Nat f :: (i -> *) -> *) where
  ap1 () = terminal
  ap2 = uncurry (&&&)

instance Monoidal (Nat f :: (i -> Constraint) -> *) where
  ap1 () = terminal
  ap2 = uncurry (&&&)

instance Monoidal (At x) where
  ap1 () = At (Const ())
  ap2 (At f, At g)= At (Lift (f, g))

-- * Monads over our kind-indexed categories

class Monoidal (m :: x -> x) => Monad (m :: x -> x) where
  join :: m (m a) ~> m a

instance (Applicative.Applicative m, Prelude.Monad m) => Monad m where
  join = Monad.join

-- * Opmonoidal functors between cocartesian categories

class (Cocartesian ((~>) :: x -> x -> *), Cocartesian ((~>) :: y -> y -> *), Functor f) => Opmonoidal (f :: x -> y) where
  op1 :: f Zero ~> Zero
  op2 :: f (a + b) ~> f a + f b

instance Opmonoidal ((,) e) where
  op1 = snd
  op2 (e,ab) = bimap ((,) e) ((,) e) ab

instance Opmonoidal Identity where
  op1 = runIdentity
  op2 = bimap Identity Identity . runIdentity

instance Opmonoidal (At x) where
  op1 (At (Const x)) = x
  op2 (At (Lift eab))= bimap At At eab

instance Opmonoidal (LiftValue (,) e) where
  op1 = snd
  op2 = Nat $ Lift . bimap Lift Lift . op2 . fmap lower . lower

-- * An

newtype An (f :: i -> *) (a :: i) = An { runAn :: f a }
_An = dimap runAn An

instance Functor f => Functor (An f) where
  fmap = _An . fmap

instance Contravariant f => Contravariant (An f) where
  contramap = _An . contramap

instance Functor An where
  fmap (Nat f) = Nat $ _An f

instance Monoidal f => Monoidal (An f) where
  ap1 = An . ap1
  ap2 = An . ap2 . bimap runAn runAn

instance Opmonoidal f => Opmonoidal (An f) where
  op1 = op1 . runAn
  op2 = bimap An An . op2 . runAn

-- a monoid object in a cartesian category
class Cartesian ((~>) :: i -> i -> *) => Monoid (m :: i) where
  one  :: One ~> m
  mult :: m * m ~> m

instance Monoid.Monoid m => Monoid m where
  one () = Monoid.mempty
  mult = uncurry Monoid.mappend

instance Monoid (ConstValue ()) where
  one = id
  mult = lambda

instance Monoid (() :: Constraint) where
  one = id
  mult = lambda

mappend :: forall (m :: i). (CCC ((~>) :: i -> i -> *), Monoid m) => m ~> m^m
mappend = curry mult

class Cocartesian ((~>) :: i -> i -> *) => Comonoid (m :: i) where
  zero   :: m ~> Zero
  comult :: m ~> m + m

instance Comonoid Void where
  zero = id
  comult = absurd

instance Comonoid (ConstValue Void) where
  zero = id
  comult = Nat $ absurd . getConst

-- instance Comonoid (ConstValue2 (ConstValue Void)) where

class Functor f => Strength (f :: x -> x) where
  strength :: a * f b ~> f (a * b)

instance Prelude.Functor f => Strength f where
  strength (a,fb) = fmap ((,) a) fb

-- what is usually called 'costrength' is more like a 'left strength' or a 'right strength'
-- repurposing this term for a real 'co'-strength
class Functor f => Costrength (f :: x -> x) where
  costrength :: f (a + b) ~> a + f b

instance Traversable.Traversable f => Costrength f where
  costrength = Traversable.sequence

ap :: forall (f :: x -> y) (a :: x) (b :: x).
      (Monoidal f, CCC ((~>) :: x -> x -> *), CCC ((~>) :: y -> y -> *))
   => f (b ^ a) ~> f b ^ f a
ap = curry (fmap apply . ap2)

return :: forall (f :: x -> x) (a :: x). (Monoidal f, Strength f, CCC ((~>) :: x -> x -> *))
      => a ~> f a
return = fmap (lambda . swap) . strength . second ap1 . rho

class (Functor f, Category ((~>) :: x -> x -> *)) => Comonad (f :: x -> x) where
  {-# MINIMAL extract, (duplicate | extend) #-}
  duplicate :: f a ~> f (f a)
  duplicate = extend id
  extend :: (f a ~> b) -> f a ~> f b
  extend f = fmap f . duplicate
  extract   :: f a ~> a

instance Comonad.Comonad f => Comonad f where
  duplicate = Comonad.duplicate
  extend = Comonad.extend
  extract = Comonad.extract

-- indexed store
data Store (s :: x -> *) (a :: x -> *) (i :: x) = Store (s ~> a) (s i)

instance Functor (Store s) where
  fmap f = Nat $ \(Store g s) -> Store (f . g) s

instance Comonad (Store s) where
  extract = Nat $ \(Store f s) -> runNat f s
  duplicate = Nat $ \(Store f s) -> Store (Nat $ Store f) s

-- The dual of Conor McBride's "Atkey" adapted to this formalism
--
-- Cokey i :: Hask -> Nat
-- Cokey :: x -> * -> x -> *
newtype Cokey i a j = Cokey { runCokey :: (i ~ j) => a }

instance Functor (Cokey i) where
  fmap f = Nat $ \xs -> Cokey $ f (runCokey xs)

instance PFunctor (Cokey i) where
  first f xs = Cokey $ f (runCokey xs)

instance QFunctor Cokey where
  second f = Nat $ \xs -> Cokey $ f (runCokey xs)

instance Monoidal (Cokey i) where
  ap1 = Nat $ \a -> Cokey (getConst a)
  ap2 = Nat $ \ab -> Cokey $ case ab of
    Lift (Cokey a, Cokey b) -> (a, b)

-- Conor McBride's "Atkey" adapted to this formalism
--
-- Key i :: Hask -> Nat
-- Key :: x -> * -> x -> *
data Key (i :: x) (a :: *) (j :: x) where
  Key :: a -> Key i a i

instance Functor (Key i) where
  fmap f = Nat $ \ (Key a) -> Key (f a)

instance PFunctor (Key i) where
  first f (Key xs) = Key (f xs)

instance QFunctor Key where
  second f = Nat $ \ (Key a) -> Key (f a)

instance Opmonoidal (Key i) where
  op1 = Nat $ \(Key v) -> Const v
  op2 = Nat $ \(Key eab) -> Lift (bimap Key Key eab)
