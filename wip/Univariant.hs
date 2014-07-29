{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, AllowAmbiguousTypes #-}
module Univariant where

import Data.Constraint (Constraint, (:-)(Sub), Dict(..), (\\), Class(cls), (:=>)(ins))
import qualified Data.Constraint as Constraint
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion
import GHC.Prim (Any)
import Prelude (($),undefined)


--------------------------------------------------------------------------------
-- * Functors
--------------------------------------------------------------------------------

class Functor' (f :: i -> j)  where
  type Dom f :: i -> i -> *
  type Cod f :: j -> j -> *
  ob :: Ob (Dom f) a => Dict (Ob (Cod f) (f a))
  fmap :: Dom f a b -> Cod f (f a) (f b)

type family NatDom (f :: (i -> j) -> (i -> j) -> *) :: (i -> i -> *) where
  NatDom (Nat p q) = p

type family NatCod (f :: (i -> j) -> (i -> j) -> *) :: (j -> j -> *) where
  NatCod (Nat p q) = q
  
type Dom2 p = NatDom (Cod p)
type Cod2 p = NatCod (Cod p)

class (Functor' p, Cod p ~ Nat (Dom2 p) (Cod2 p)) => Bifunctor' (p :: i -> j -> k) where
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

type Iso c d e s t a b = forall p. (Profunctor p, Dom p ~ Op c, Dom2 p ~ d, Cod2 p ~ e) => e (p a b) (p s t)

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

class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous c a

instance Functor' (Vacuous c) where
  type Dom (Vacuous c) = c
  type Cod (Vacuous c) = (:-)
  ob = Dict
  fmap _ = Sub Dict

--------------------------------------------------------------------------------
-- * Constraint
--------------------------------------------------------------------------------


instance Functor' (:-) where
  type Dom (:-) = Op (:-)
  type Cod (:-) = Nat (:-) (->) -- copresheaves
  ob = Dict
  fmap (Op f) = Nat (. f)

instance Functor' ((:-) b) where
  type Dom ((:-) a) = (:-)
  type Cod ((:-) a) = (->)
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


instance Functor' (->) where 
  type Dom (->) = Op (->)
  type Cod (->) = Nat (->) (->)
  ob = Dict
  fmap (Op f) = Nat (. f)

instance Functor' ((->)a) where
  type Dom ((->) a) = (->)
  type Cod ((->) a) = (->)
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

instance Category p => Functor' (Op p) where
  type Dom (Op p) = Op (Op p)
  type Cod (Op p) = Nat (Op p) (->)
  ob = Dict
  fmap (Op f) = Nat (. f)

instance Category p => Bifunctor' (Op p) where
  ob2 = Dict
  bimap (Op (Op f)) g (Op h) = Op $ bimap g f h

instance Category p => Functor' (Op p a) where
  type Dom (Op p a) = Op p
  type Cod (Op p a) = (->)
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

type Copresheaves p = Nat p (->)
type Presheaves p = Nat (Op p) (->)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

instance Functor' (FunctorOf p q) where
  type Dom (FunctorOf p q) = Nat p q
  type Cod (FunctorOf p q) = (:-)
  ob = Dict
  fmap Nat{} = Sub Dict

instance (Category' p, Category q) => Functor' (Nat p q) where
  type Dom (Nat p q) = Op (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  ob = Dict
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Bifunctor' (Nat p q) where
  ob2 = Dict
  bimap (Op (Nat f)) (Nat g) (Nat h) = Nat (bimap (Op f) g h)

instance (Category' p, Category q) => Functor' (Nat p q a) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
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
-- * Prof
--------------------------------------------------------------------------------

data Prof (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j -> *) (g :: i -> j -> *) where
  Prof :: (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Profunctor g, Dom g ~ Op p, Dom2 g ~ q, Cod2 f ~ (->), Cod2 g ~ (->)) => { runProf :: forall a b. (Ob p a, Ob q b) => f a b -> g a b } -> Prof p q f g

class    (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ (->)) => ProfunctorOf p q f
instance (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ (->)) => ProfunctorOf p q f

instance Functor' (ProfunctorOf p q) where
  type Dom (ProfunctorOf p q) = Prof p q
  type Cod (ProfunctorOf p q) = (:-)
  ob = Dict
  fmap Prof{} = Sub Dict

instance (Category' p, Category q) => Functor' (Prof p q) where
  type Dom (Prof p q) = Op (Prof p q)
  type Cod (Prof p q) = Nat (Prof p q) (->)
  ob = Dict
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Bifunctor' (Prof p q) where
  ob2 = Dict
  bimap (Op (Prof f)) (Prof g) (Prof h) = Prof (bimap (Op f) g h)

instance (Category' p, Category q) => Functor' (Prof p q a) where
  type Dom (Prof p q f) = Prof p q
  type Cod (Prof p q f) = (->)
  ob = Dict
  fmap = (.)

instance (Category' p, Category' q) => Category' (Prof p q) where
   type Ob (Prof p q) = ProfunctorOf p q
   id = Prof id
   observe Prof{} = Dict
   Prof f . Prof g = Prof (f . g)

prof :: (Category p, Category q) => Dict (Category (Prof p q))
prof = Dict

--------------------------------------------------------------------------------
-- * Monoidal Tensors
--------------------------------------------------------------------------------

class (Bifunctor p, Dom p ~ Dom2 p, Dom p ~ Cod2 p) => Semitensor p where
  associate :: Iso (Dom p) (Dom p) (Dom p) (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))

type family I (p :: i -> i -> i) :: i

class Semitensor p => Tensor' p where
  lambda :: Iso (Dom p) (Dom p) (Dom p) (p (I p) a) (p (I p) a') a a'
  rho    :: Iso (Dom p) (Dom p) (Dom p) (p a (I p)) (p a' (I p)) a a'

class (Monoid' p (I p), Tensor' p) => Tensor p
class (Monoid' p (I p), Tensor' p) => Tensor p

class Semitensor p => Semigroup p m where
  mu :: Dom p (p m m) m

class (Semigroup p m, Tensor' p) => Monoid' p m where
  eta :: Proxy p -> Dom p (I p) m

class Semitensor p => Cosemigroup p w where
  delta :: Dom p w (p w w)

class (Cosemigroup p m, Tensor p) => Comonoid p m where
  epsilon :: Proxy p -> Dom p m (I p)

--------------------------------------------------------------------------------
-- * (,)
--------------------------------------------------------------------------------

instance Bifunctor' (,) where
  ob2 = Dict
  bimap f g (a,b) = (f a, g b)
  
instance Functor' (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  ob = Dict
  fmap f = Nat $ \(a,b) -> (f a, b)

instance Functor' ((,) a) where
  type Dom ((,) a) = (->)
  type Cod ((,) a) = (->)
  ob = Dict
  fmap f (a,b) = (a, f b)

instance Semitensor (,) where
  associate = dimap (\((a,b),c) -> (a,(b,c))) (\(a,(b,c)) -> ((a,b),c))

-- | Profunctor composition is the composition for a relative monad; composition with the left kan extension along the (contravariant) yoneda embedding

{-
data Procompose (p :: j -> k -> *) (q :: i -> j -> *) (a :: i) (b :: k) where
  Procompose :: p x b -> q a x -> Procompose p q a b

  
associateProcompose :: Iso (Procompose (Procompose p q) r) (Procompose (Procompose p' q') r')
                           (Procompose p (Procompose q r)) (Procompose p' (Procompose q' r'))
associateProcompose = dimap
  (Prof $ \ (Procompose (Procompose a b) c) -> Procompose a (Procompose b c))
  (Prof $ \ (Procompose a (Procompose b c)) -> Procompose (Procompose a b) c)
-}
