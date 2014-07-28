{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds #-}
module Lame where

import Data.Constraint (Constraint, (:-)(Sub), Dict(..), (\\), Class(cls), (:=>)(ins))
import qualified Data.Constraint as Constraint
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion
import GHC.Prim (Any)
import Prelude (($))

type family Hom :: i -> i -> j
type instance Hom = (->)
type instance Hom = (:-)
type instance Hom = Nat (~>) (~>)

type (~>) = (Hom :: i -> i -> *) -- use sparingly

type family Dom  (f :: i -> j)      :: i -> i -> *
type family Cod  (f :: i -> j)      :: j -> j -> *
type family Dom2 (f :: i -> j -> k) :: j -> j -> *
type family Cod2 (f :: i -> j -> k) :: k -> k -> *

class Discrete' f where
  ob :: Ob (Dom f) a :- Ob (Cod f) (f a)

class Discrete' f => Functor' f where
  fmap :: Dom f a b -> Cod f (f a) (f b)

class Discrete' f => Contravariant' f where
  contramap :: Dom f a b -> Cod f (f b) (f a)

class (Functor' f, Contravariant' f) => Phantom' f
instance (Functor' f, Contravariant' f) => Phantom' f

class Profunctor' p where
  dimap :: Dom p a b -> Dom2 p c d -> Cod2 p (p b c) (p a d)

type Iso s t a b = forall p. Profunctor p => Cod2 p (p a b) (p s t)

class Bifunctor' p where
  bimap :: Dom p a b -> Dom2 p c d -> Cod2 p (p a c) (p b d)

class Category' (p :: i -> i -> *) where
  type Ob p :: i -> Constraint
  id  :: Ob p a => p a a
  -- equiv  :: Coercible a b => p a b
  observe :: p a b -> Dict (Ob p a, Ob p b)
  (.) :: p b c -> p a b -> p a c

-- break cycles for #9200

class (Discrete' f, Category' (Dom f), Category' (Cod f)) => Discrete f
instance (Discrete' f, Category' (Dom f), Category' (Cod f)) => Discrete f

class (Contravariant' f, Category' (Dom f), Category' (Cod f)) => Contravariant f
instance (Contravariant' f, Category' (Dom f), Category' (Cod f)) => Contravariant f

class (Functor' f, Category' (Dom f), Category' (Cod f)) => Functor f
instance (Functor' f, Category' (Dom f), Category' (Cod f)) => Functor f

class (Phantom' f, Category' (Dom f), Category' (Cod f)) => Phantom f
instance (Phantom' f, Category' (Dom f), Category' (Cod f)) => Phantom f

class (Profunctor' p, Contravariant' p, Category' (Cod p), Category' (Dom p), Category' (Dom2 p), Category' (Cod2 p)) => Profunctor p -- explicitly Contravariant
instance (Profunctor' p, Contravariant' p, Category (Cod p), Category' (Dom p), Category' (Dom2 p), Category' (Cod2 p)) => Profunctor p

class (Bifunctor' p, Functor' p, Category' (Cod p), Category' (Dom p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor p -- explicit Functor
instance (Bifunctor' p, Functor' p, Category' (Cod p), Category' (Dom p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor p

class (Category' p, Profunctor' p, Dom p ~ p, Cod p ~ Nat p Hom, Dom2 p ~ p, Cod2 p ~ (->), Phantom' (Ob p)) => Category p
instance (Category' p, Profunctor' p, Dom p ~ p, Cod p ~ Nat p Hom, Dom2 p ~ p, Cod2 p ~ (->), Phantom' (Ob p)) => Category p

class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous (c :: i -> i -> *) (a :: i)

type instance Dom (Vacuous c) = c
type instance Cod (Vacuous c) = (:-)

instance Discrete' (Vacuous c) where
  ob = Sub Dict

instance Functor' (Vacuous c) where
  fmap _ = Sub Dict

instance Contravariant' (Vacuous c) where
  contramap _ = Sub Dict

type instance Dom (:-)    = (:-)
type instance Cod (:-)    = Nat (:-) (->) -- copresheaves
type instance Dom2 (:-)   = (:-)
type instance Dom ((:-)a) = (:-)
type instance Cod2 (:-)   = (->)
type instance Cod ((:-)a) = (->)

instance Discrete' (:-) where ob = Sub Dict
instance Contravariant' (:-) where contramap f = Nat (. f)
instance Profunctor' (:-) where dimap f g h = g . h . f
instance Discrete' ((:-) b) where ob = Sub Dict
instance Functor' ((:-) b) where fmap = (.)

instance Category' (:-) where
  type Ob (:-) = Vacuous (:-)
  id = Constraint.refl
  observe _ = Dict
  (.) = Constraint.trans

constraint :: Dict (Category (:-))
constraint = Dict

type instance Dom (->)    = (->)
type instance Cod (->)    = Nat (->) (->) -- copresheaves
type instance Dom2 (->)   = (->)
type instance Dom ((->)a) = (->)
type instance Cod2 (->)   = (->)
type instance Cod ((->)a) = (->)

instance Discrete' (->) where ob = Sub Dict
instance Contravariant' (->) where contramap f = Nat (. f)
instance Discrete' ((->) b) where ob = Sub Dict
instance Functor' ((->) b) where fmap = (.)
instance Profunctor' (->) where dimap f g h = g . h . f

instance Category' (->) where
  type Ob (->) = Vacuous (->)
  id x = x
  observe _ = Dict
  (.) f g x = f (g x)

hask :: Dict (Category (->))
hask = Dict

data Nat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j) (g :: i -> j) where
  Nat :: (Functor' f, Dom f ~ p, Cod f ~ q, Functor' g, Dom g ~ p, Cod g ~ q) => { runNat :: forall a. Ob p a => q (f a) (g a) } -> Nat p q f g

type instance Dom (Nat p q)   = Nat p q
type instance Cod (Nat p q)   = Nat (Nat p q) (->)
type instance Dom2 (Nat p q)  = Nat p q
type instance Cod2 (Nat p q)  = (->)
type instance Dom (Nat p q f) = Nat p q
type instance Cod (Nat p q f) = (->)

type Copresheaves p = Nat p (->)

type instance Dom (FunctorOf p q) = Nat p q
type instance Cod (FunctorOf p q) = (:-)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

instance Discrete' (FunctorOf p q) where
  ob = Sub Dict
  
instance (Category' p, Category' q) => Functor' (FunctorOf p q) where
  fmap Nat{} = Sub Dict

instance (Category' p, Category' q) => Contravariant' (FunctorOf p q) where
  contramap Nat{} = Sub Dict

instance (Category' p, Category q) => Profunctor' (Nat p q) where
  dimap (Nat f) (Nat g) (Nat h) = Nat (dimap f g h)

instance (Category' p, Category' q) => Category' (Nat p q) where
   type Ob (Nat p q) = FunctorOf p q
   id = Nat id1 where
     id1 :: forall f x. (Discrete' f, Dom f ~ p, Cod f ~ q, Ob p x) => q (f x) (f x)
     id1 = id \\ (ob :: Ob p x :- Ob q (f x))
   observe Nat{} = Dict
   Nat f . Nat g = Nat (f . g)

nat :: (Category p, Category q) => Dict (Category (Nat p q))
nat = Dict

{-
type family Op (p :: i -> j -> *) :: j -> i -> * where
  Op (Op1 p) = p
  Op = Op1
-}

newtype Op (p :: i -> i -> *) (a :: i) (b :: i) = Op { getOp :: p b a }

-- Op :: Prof^op -> Prof
-- type instance Dom Op       = Prof
-- type instance Cod Op       = Prof
type instance Dom (Op p)   = Op (Dom p)
type instance Cod (Op p)   = Nat (Op (Dom p)) (->)
type instance Dom (Op p a) = Op (Dom p)
type instance Dom2 (Op p)  = Op (Dom p)
type instance Cod2 (Op p)  = (->)
type instance Cod (Op p a) = (->)

instance Contravariant Op 
instance Category p => Discrete' (Op p) where ob = Sub Dict
instance Category p => Contravariant' (Op p) where contramap pab = Nat (. pab)
instance Category p => Profunctor' (Op p) where dimap (Op f) (Op g) (Op h) = Op (dimap g f h)
instance Discrete' (Op p a) where ob = Sub Dict 
instance Category p => Functor' (Op p a) where fmap = (.)
instance Category p => Category' (Op p) where
  type Ob (Op p) = Ob p
  id = Op id
  Op f . Op g = Op (g . f)
  observe (Op f) = case observe f of
    Dict -> Dict

-- op :: (Functor' (Ob p), Contravariant' (Ob p), p ~ Dom p, p ~ Dom2 p, Category' p) => Dict (Category (Op p))
op :: Category p => Dict (Category (Op p))
op = Dict
