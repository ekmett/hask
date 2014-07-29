{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds #-}
module Univariant where

import Data.Constraint (Constraint, (:-)(Sub), Dict(..), (\\), Class(cls), (:=>)(ins))
import qualified Data.Constraint as Constraint
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion
import GHC.Prim (Any)
import Prelude (($),undefined)

type family Dom  (f :: i -> j)      :: i -> i -> *
type family Cod  (f :: i -> j)      :: j -> j -> *
type family Dom2 (f :: i -> j -> k) :: j -> j -> *
type family Cod2 (f :: i -> j -> k) :: k -> k -> *

--------------------------------------------------------------------------------
-- * Functors
--------------------------------------------------------------------------------

class Functor' f where
  ob :: Ob (Dom f) a => Dict (Ob (Cod f) (f a))
  fmap :: Dom f a b -> Cod f (f a) (f b)

class Bifunctor' p where
  ob2 :: (Ob (Dom p) a, Ob (Dom2 p) b) => Dict (Ob (Cod2 p) (p a b))
  bimap :: Dom p a b -> Dom2 p c d -> Cod2 p (p a c) (p b d)

--------------------------------------------------------------------------------
-- * Contravariance
--------------------------------------------------------------------------------

newtype Op (p :: i -> i -> *) (a :: i) (b :: i) = Op { getOp :: p b a }

type family UnOp (p :: i -> i -> *) :: i -> i -> * where
  UnOp (Op p) = p
  UnOp p = Op p

type Opd f = UnOp (Dom f)

class (Dom p ~ Op (Opd p)) => Contra p
instance (Dom p ~ Op (Opd p)) => Contra p

class (Contra f, Functor' f) => Contravariant' f
instance (Contra f, Functor' f) => Contravariant' f

contramap :: Contravariant' f => Opd f b a -> Cod f (f a) (f b)
contramap = fmap . Op

class (Contra p, Bifunctor' p) => Profunctor' p 
instance (Contra p, Bifunctor' p) => Profunctor' p 

dimap :: Profunctor' p => Opd p b a -> Dom2 p c d -> Cod2 p (p a c) (p b d)
dimap = bimap . Op

type Iso s t a b = forall p. Profunctor' p => Cod2 p (p a b) (p s t)

--------------------------------------------------------------------------------
-- * Category
--------------------------------------------------------------------------------

class Category' (p :: i -> i -> *) where
  type Ob p :: i -> Constraint
  id  :: Ob p a => p a a
  observe :: p a b -> Dict (Ob p a, Ob p b)
  (.) :: p b c -> p a b -> p a c
  -- equiv  :: Coercible a b => p a b

--------------------------------------------------------------------------------
-- * Circular Definition, See Definition, Circular
--------------------------------------------------------------------------------

class (Functor' f, Category' (Dom f), Category' (Cod f)) => Functor f
instance (Functor' f, Category' (Dom f), Category' (Cod f)) => Functor f

class (Contra f, Functor f) => Contravariant f
instance (Contra f, Functor f) => Contravariant f

class (Bifunctor' p, Functor' p, Category' (Cod p), Category' (Dom p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor p
instance (Bifunctor' p, Functor' p, Category' (Cod p), Category' (Dom p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor p

class (Contra f, Bifunctor f) => Profunctor f
instance (Contra f, Bifunctor f) => Profunctor f

class (Category' p, Profunctor' p, Dom p ~ Op p, Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->), Functor' (Ob p)) => Category p
instance (Category' p, Profunctor' p, Dom p ~ Op p, Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->), Functor' (Ob p)) => Category p

type instance Dom (Vacuous c) = c
type instance Cod (Vacuous c) = (:-)

class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous c a

instance Functor' (Vacuous c) where
  ob = Dict
  fmap _ = Sub Dict

--------------------------------------------------------------------------------
-- * Constraint
--------------------------------------------------------------------------------

type instance Dom (:-)    = Op (:-)
type instance Cod (:-)    = Nat (:-) (->) -- copresheaves
type instance Dom2 (:-)   = (:-)
type instance Dom ((:-)a) = (:-)
type instance Cod2 (:-)   = (->)
type instance Cod ((:-)a) = (->)

instance Functor' (:-) where
  ob = Dict
  fmap (Op f) = Nat (. f)

instance Functor' ((:-) b) where
  ob = Dict
  fmap = (.)

instance Bifunctor' (:-) where
  ob2 = Dict
  bimap (Op f) g h = g . h . f

instance Category' (:-) where
  type Ob (:-) = Vacuous (:-)
  id = Constraint.refl
  observe _ = Dict
  (.) = Constraint.trans

constraint :: Dict (Category (:-))
constraint = Dict

--------------------------------------------------------------------------------
-- * Hask
--------------------------------------------------------------------------------

type instance Dom (->)    = Op (->)
type instance Cod (->)    = Nat (->) (->)
type instance Dom2 (->)   = (->)
type instance Dom ((->)a) = (->)
type instance Cod2 (->)   = (->)
type instance Cod ((->)a) = (->)

instance Functor' (->) where 
  ob = Dict
  fmap (Op f) = Nat (. f)

instance Functor' ((->) b) where
  ob = Dict
  fmap = (.)

instance Bifunctor' (->) where
  ob2 = Dict
  bimap (Op f) g h = g . h . f

instance Category' (->) where
  type Ob (->) = Vacuous (->)
  id x = x
  observe _ = Dict
  (.) f g x = f (g x)

hask :: Dict (Category (->))
hask = Dict

--------------------------------------------------------------------------------
-- * Op
--------------------------------------------------------------------------------

type instance Dom (Op p)   = Op (Op p)
type instance Cod (Op p)   = Nat (Op p) (->)
type instance Dom (Op p a) = Op p
type instance Dom2 (Op p)  = Op p
type instance Cod2 (Op p)  = (->)
type instance Cod (Op p a) = (->)

instance Category p => Functor' (Op p) where
  ob = Dict
  fmap (Op f) = Nat (. f)

instance Category p => Bifunctor' (Op p) where
  ob2 = Dict
  bimap (Op (Op f)) g (Op h) = Op $ bimap g f h

instance Category p => Functor' (Op p a) where
  ob = Dict 
  fmap = (.)

instance Category p => Category' (Op p) where
  type Ob (Op p) = Ob p
  id = Op id
  Op f . Op g = Op (g . f)
  observe (Op f) = case observe f of
    Dict -> Dict

op :: Category p => Dict (Category (Op p))
op = Dict

--------------------------------------------------------------------------------
-- * Nat
--------------------------------------------------------------------------------

data Nat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j) (g :: i -> j) where
  Nat :: (Functor f, Dom f ~ p, Cod f ~ q, Functor g, Dom g ~ p, Cod g ~ q) => { runNat :: forall a. Ob p a => q (f a) (g a) } -> Nat p q f g

type instance Dom (Nat p q)   = Op (Nat p q)
type instance Cod (Nat p q)   = Nat (Nat p q) (->)
type instance Dom2 (Nat p q)  = Nat p q
type instance Cod2 (Nat p q)  = (->)
type instance Dom (Nat p q f) = Nat p q
type instance Cod (Nat p q f) = (->)

type Copresheaves p = Nat p (->)
type Presheaves p = Nat (Op p) (->)

type instance Dom (FunctorOf p q) = Nat p q
type instance Cod (FunctorOf p q) = (:-)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

instance Functor' (FunctorOf p q) where
  ob = Dict
  fmap Nat{} = Sub Dict

instance (Category' p, Category q) => Functor' (Nat p q) where
  ob = Dict
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Bifunctor' (Nat p q) where
  ob2 = Dict
  bimap (Op (Nat f)) (Nat g) (Nat h) = Nat (bimap (Op f) g h)

instance (Category' p, Category q) => Functor' (Nat p q a) where
  ob = Dict
  fmap = (.)

instance (Category' p, Category' q) => Category' (Nat p q) where
   type Ob (Nat p q) = FunctorOf p q
   id = Nat id1 where
     id1 :: forall f x. (Functor' f, Dom f ~ p, Cod f ~ q, Ob p x) => q (f x) (f x)
     id1 = id \\ (ob1 :: Ob p x :- Ob q (f x))
     ob1 :: Functor' f => Ob (Dom f) x :- Ob (Cod f) (f x)
     ob1 = Sub ob
   observe Nat{} = Dict
   Nat f . Nat g = Nat (f . g)

nat :: (Category p, Category q) => Dict (Category (Nat p q))
nat = Dict

--------------------------------------------------------------------------------
-- * Pronat
--------------------------------------------------------------------------------

data Pronat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j -> *) (g :: i -> j -> *) where
  Pronat :: (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Profunctor g, Dom g ~ Op p, Dom2 g ~ q, Cod2 f ~ (->), Cod2 g ~ (->)) => { runPronat :: forall a b. (Ob p a, Ob q b) => f a b -> g a b } -> Pronat p q f g

type instance Dom  (Pronat p q)   = Op (Pronat p q)
type instance Cod  (Pronat p q)   = Nat (Pronat p q) (->)
type instance Dom2 (Pronat p q)   = Pronat p q
type instance Cod2 (Pronat p q)   = (->)
type instance Dom  (Pronat p q f) = Pronat p q
type instance Cod  (Pronat p q f) = (->)

type instance Dom (ProfunctorOf p q) = Pronat p q
type instance Cod (ProfunctorOf p q) = (:-)

class    (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ (->)) => ProfunctorOf p q f
instance (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ (->)) => ProfunctorOf p q f

instance Functor' (ProfunctorOf p q) where
  ob = Dict
  fmap Pronat{} = Sub Dict

instance (Category' p, Category q) => Functor' (Pronat p q) where
  ob = Dict
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Bifunctor' (Pronat p q) where
  ob2 = Dict
  bimap (Op (Pronat f)) (Pronat g) (Pronat h) = Pronat (bimap (Op f) g h)

instance (Category' p, Category q) => Functor' (Pronat p q a) where
  ob = Dict
  fmap = (.)

instance (Category' p, Category' q) => Category' (Pronat p q) where
   type Ob (Pronat p q) = ProfunctorOf p q
   id = Pronat id
   observe Pronat{} = Dict
   Pronat f . Pronat g = Pronat (f . g)

pronat :: (Category p, Category q) => Dict (Category (Pronat p q))
pronat = Dict

data Prof (p :: j -> k -> *) (q :: i -> j -> *) (a :: i) (b :: k) where
  Prof :: p x b -> q a x -> Prof p q a b


