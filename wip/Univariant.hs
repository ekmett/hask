{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, AllowAmbiguousTypes, LambdaCase, DefaultSignatures, EmptyCase #-}
module Univariant where

import Data.Constraint (Constraint, (:-)(Sub), Dict(..), (\\), Class(cls), (:=>)(ins))
import qualified Data.Constraint as Constraint
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Data.Proxy (Proxy(..))
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion
import Data.Void
import GHC.Prim (Any, Coercible, coerce)
import Prelude (($),undefined,Either(..),error)
import qualified Prelude
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- * Categories (Part 1)
--------------------------------------------------------------------------------

-- | The <http://ncatlab.org/nlab/show/Yoneda+embedding Yoneda embedding>.
--
-- Yoneda_C :: C -> [ C^op, Set ]
newtype Yoneda (p :: i -> i -> *) (a :: i) (b :: i) = Op { getOp :: p b a }

type family Op (p :: i -> i -> *) :: i -> i -> * where
  Op (Yoneda p) = p
  Op p = Yoneda p

-- | Side-conditions moved to 'Functor' to work around GHC bug #9200.
--
-- You should produce instances of 'Category'' and consume instances of 'Category'.
--
-- All of our categories are "locally small", and we curry the Hom-functor
-- as a functor to the category of copresheaves rather than present it as a
-- bifunctor directly. The benefit of this encoding is that a bifunctor is
-- just a functor to a functor category!
--
-- C :: C^op -> [ C, Set ]
class Category' (p :: i -> i -> *) where
  type Ob p :: i -> Constraint
  id :: Ob p a => p a a
  observe :: p a b -> Dict (Ob p a, Ob p b)
  (.) :: p b c -> p a b -> p a c

  unop :: Op p b a -> p a b
  default unop :: Op p ~ Yoneda p => Op p b a -> p a b
  unop = getOp

  op :: p b a -> Op p a b
  default op :: Op p ~ Yoneda p => p b a -> Op p a b
  op = Op

type Endo p a = p a a

--------------------------------------------------------------------------------
-- * Functors
--------------------------------------------------------------------------------

class (Category' (Dom f), Category' (Cod f)) => Functor (f :: i -> j) where
  type Dom f :: i -> i -> *
  type Cod f :: j -> j -> *
  fmap :: Dom f a b -> Cod f (f a) (f b)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

ob :: forall f a. Functor f => Ob (Dom f) a :- Ob (Cod f) (f a)
ob = Sub $ case observe (fmap (id :: Dom f a a) :: Cod f (f a) (f a)) of
  Dict -> Dict

data Nat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j) (g :: i -> j) where
  Nat :: ( FunctorOf p q f
         , FunctorOf p q g
         ) => {
           runNat :: forall a. Ob p a => q (f a) (g a)
         } -> Nat p q f g

type NatId p = Endo (Nat (Dom p) (Cod p)) p

obOf :: (Category (Dom f), Category (Cod f)) => NatId f -> Endo (Dom f) a
     -> Dict (Ob (Nat (Dom f) (Cod f)) f, Ob (Dom f) a, Ob (Cod f) (f a))
obOf f a = case observe f of
  Dict -> case observe a of
    Dict -> case observe (f ! a) of
      Dict -> Dict

type Copresheaves p = Nat p (->)
type Presheaves p = Nat (Op p) (->)

instance (Category' p, Category' q) => Functor (FunctorOf p q) where
  type Dom (FunctorOf p q) = Nat p q
  type Cod (FunctorOf p q) = (:-)
  fmap Nat{} = Sub Dict

--------------------------------------------------------------------------------
-- * Bifunctors
--------------------------------------------------------------------------------

type family NatDom (f :: (i -> j) -> (i -> j) -> *) :: (i -> i -> *) where
  NatDom (Nat p q) = p

type family NatCod (f :: (i -> j) -> (i -> j) -> *) :: (j -> j -> *) where
  NatCod (Nat p q) = q

type Dom2 p = NatDom (Cod p)
type Cod2 p = NatCod (Cod p)

class (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)
instance  (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)

fmap1 :: forall p a b c. (Bifunctor p, Ob (Dom p) c) => Dom2 p a b -> Cod2 p (p c a) (p c b)
fmap1 f = case ob :: Ob (Dom p) c :- FunctorOf (Dom2 p) (Cod2 p) (p c) of
  Sub Dict -> fmap f

bimap :: Bifunctor p => Dom p a b -> Dom2 p c d -> Cod2 p (p a c) (p b d)
bimap f g = case observe f of
  Dict -> case observe g of
    Dict -> runNat (fmap f) . fmap1 g

type Opd f = Op (Dom f)

contramap :: Functor f => Opd f b a -> Cod f (f a) (f b)
contramap = fmap . unop

-- | E-Enriched profunctors f : C -/-> D are represented by a functor of the form:
--
-- C^op -> [ D, E ]
--
-- The variance here matches Haskell's order, which means that the contravariant
-- argument comes first!

dimap :: Bifunctor p => Opd p b a -> Dom2 p c d -> Cod2 p (p a c) (p b d)
dimap = bimap . unop

type Iso
  (c :: i -> i -> *) (d :: j -> j -> *) (e :: k -> k -> *)
  (s :: i) (t :: j) (a :: i) (b :: j) = forall (p :: i -> j -> k).
  (Bifunctor p, Opd p ~ c, Dom2 p ~ d, Cod2 p ~ e) => e (p a b) (p s t)

--------------------------------------------------------------------------------
-- * Categories (Part 2)
--------------------------------------------------------------------------------

class    (Category' p, Bifunctor p, Dom p ~ Op p, p ~ Op (Dom p), Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->)) => Category'' p
instance (Category' p, Bifunctor p, Dom p ~ Op p, p ~ Op (Dom p), Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->)) => Category'' p

-- | The full definition for a (locally-small) category.
class    (Category'' p, Category'' (Op p), p ~ Op (Op p), Ob p ~ Ob (Op p)) => Category p
instance (Category'' p, Category'' (Op p), p ~ Op (Op p), Ob p ~ Ob (Op p)) => Category p

--------------------------------------------------------------------------------
-- * Fully Faithful Functors
--------------------------------------------------------------------------------

class Functor f => FullyFaithful f where
  unfmap :: Cod f (f a) (f b) -> Dom f a b

instance FullyFaithful Dict where
  unfmap f = Sub $ f Dict

--------------------------------------------------------------------------------
-- * Vacuous
--------------------------------------------------------------------------------

class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous c a

instance Functor Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap f Dict = case f of Sub g -> g

instance (Category' c, Ob c ~ Vacuous c) => Functor (Vacuous c) where
  type Dom (Vacuous c) = c
  type Cod (Vacuous c) = (:-)
  fmap _ = Sub Dict

--------------------------------------------------------------------------------
-- * The Category of Constraints
--------------------------------------------------------------------------------

instance Functor (:-) where
  type Dom (:-) = Op (:-)
  type Cod (:-) = Nat (:-) (->) -- copresheaves
  fmap (Op f) = Nat (. f)

instance FullyFaithful (:-) where
  unfmap (Nat f) = Op (f id)

instance Functor ((:-) b) where
  type Dom ((:-) a) = (:-)
  type Cod ((:-) a) = (->)
  fmap = (.)

instance Category' (:-) where
  type Ob (:-) = Vacuous (:-)
  id = Constraint.refl
  observe _ = Dict
  (.) = Constraint.trans
  unop = getOp

constraint :: Dict (Category (:-))
constraint = Dict

sub :: (a => Proxy a -> Dict b) -> a :- b
sub k = Sub (k Proxy)

--------------------------------------------------------------------------------
-- * Hask
--------------------------------------------------------------------------------

instance Functor (->) where
  type Dom (->) = Op (->)
  type Cod (->) = Nat (->) (->)
  fmap (Op f) = Nat (. f)

instance FullyFaithful (->) where
  unfmap (Nat f) = Op (f id)

instance Functor ((->)a) where
  type Dom ((->) a) = (->)
  type Cod ((->) a) = (->)
  fmap = (.)

instance Category' (->) where
  type Ob (->) = Vacuous (->)
  id x = x
  observe _ = Dict
  (.) f g x = f (g x)
  unop = getOp

hask :: Dict (Category (->))
hask = Dict

--------------------------------------------------------------------------------
-- * Yoneda :: i -> [ Op i, Set ]
--------------------------------------------------------------------------------

instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p) where
  type Dom (Yoneda p) = p
  type Cod (Yoneda p) = Nat (Yoneda p) (->)
  fmap f = Nat (. Op f)

instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p a) where
  type Dom (Yoneda p a) = Yoneda p
  type Cod (Yoneda p a) = (->)
  fmap = (.)

instance (Category p, Op p ~ Yoneda p) => Category' (Yoneda p) where
  type Ob (Yoneda p) = Ob p
  id = Op id
  Op f . Op g = Op (g . f)
  observe (Op f) = case observe f of
    Dict -> Dict
  unop = Op
  op = getOp

opDict :: (Category p, Op p ~ Yoneda p) => Dict (Category (Yoneda p))
opDict = Dict

yoneda :: forall p f g a b. (Ob p a, FunctorOf p (->) g, FunctorOf p (->) (p b))
       => Iso (->) (->) (->)
          (Nat p (->) (p a) f)
          (Nat p (->) (p b) g)
          (f a)
          (g b)
yoneda = dimap hither yon where
  hither :: Nat p (->) (p a) f -> f a
  hither (Nat f) = f id
  yon :: g b -> Nat p (->) (p b) g
  yon gb = Nat $ \pba -> fmap pba gb

--------------------------------------------------------------------------------
-- * Nat
--------------------------------------------------------------------------------

instance (Category' p, Category q) => Functor (Nat p q) where
  type Dom (Nat p q) = Op (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Functor (Nat p q a) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  fmap = (.)

instance (Category' p, Category' q) => Category' (Nat p q) where
   type Ob (Nat p q) = FunctorOf p q
   id = Nat id1 where
     id1 :: forall f x. (Functor f, Dom f ~ p, Cod f ~ q, Ob p x) => q (f x) (f x)
     id1 = id \\ (ob :: Ob p x :- Ob q (f x))
   observe Nat{} = Dict
   Nat f . Nat g = Nat (f . g)
   unop = getOp

nat :: (Category p ,Category q, FunctorOf p q f, FunctorOf p q g) => (forall a. Ob p a => Endo p a -> q (f a) (g a)) -> Nat p q f g
nat k = Nat (k id)

natDict :: (Category p, Category q) => Dict (Category (Nat p q))
natDict = Dict

infixr 1 !
(!) :: Nat p q f g -> p a a -> q (f a) (g a)
Nat n ! f = case observe f of
  Dict -> n

--------------------------------------------------------------------------------
-- * Monoidal Tensors and Monoids
--------------------------------------------------------------------------------

class (Bifunctor p, Dom p ~ Dom2 p, Dom p ~ Cod2 p) => Semitensor p where
  associate :: (Ob (Dom p) a, Ob (Dom p) b, Ob (Dom p) c, Ob (Dom p) a', Ob (Dom p) b', Ob (Dom p) c')
            => Iso (Dom p) (Dom p) (->) (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))

type family I (p :: i -> i -> i) :: i

class Semitensor p => Tensor' p where
  lambda :: (Ob (Dom p) a, Ob (Dom p) a') => Iso (Dom p) (Dom p) (->) (p (I p) a) (p (I p) a') a a'
  rho    :: (Ob (Dom p) a, Ob (Dom p) a') => Iso (Dom p) (Dom p) (->) (p a (I p)) (p a' (I p)) a a'

class (Monoid' p (I p), Tensor' p) => Tensor p
instance (Monoid' p (I p), Tensor' p) => Tensor p

class Semitensor p => Semigroup p m where
  mu :: Dom p (p m m) m

class (Semigroup p m, Tensor' p) => Monoid' p m where
  eta :: NatId p -> Dom p (I p) m

class (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Monoid' p m) => Monoid p m
instance (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Monoid' p m) => Monoid p m

class Semitensor p => Cosemigroup p w where
  delta :: Dom p w (p w w)

class (Cosemigroup p w, Tensor' p) => Comonoid' p w where
  epsilon :: NatId p -> Dom p w (I p)

class (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Comonoid' p w) => Comonoid p w
instance (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Comonoid' p w) => Comonoid p w

--------------------------------------------------------------------------------
-- * (&)
--------------------------------------------------------------------------------

class (p, q) => p & q
instance (p, q) => p & q

instance Functor (&) where
  type Dom (&) = (:-)
  type Cod (&) = Nat (:-) (:-)
  fmap f = Nat $ Sub $ Dict \\ f

instance Functor ((&) a) where
  type Dom ((&) a) = (:-)
  type Cod ((&) a) = (:-)
  fmap f = Sub $ Dict \\ f

instance Semitensor (&) where
  associate = dimap (Sub Dict) (Sub Dict)

type instance I (&) = (() :: Constraint)

instance Tensor' (&) where
  lambda = dimap (Sub Dict) (Sub Dict)
  rho    = dimap (Sub Dict) (Sub Dict)

instance Semigroup (&) a where
  mu = Sub Dict

instance Monoid' (&) (() :: Constraint) where
  eta _ = Sub Dict

instance Cosemigroup (&) a where
  delta = Sub Dict

instance Comonoid' (&) a where
  epsilon _ = Sub Dict

--------------------------------------------------------------------------------
-- * (,) and ()
--------------------------------------------------------------------------------

instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat $ \(a,b) -> (f a, b)

instance Functor ((,) a) where
  type Dom ((,) a) = (->)
  type Cod ((,) a) = (->)
  fmap f (a,b) = (a, f b)

instance Semitensor (,) where
  associate = dimap (\((a,b),c) -> (a,(b,c))) (\(a,(b,c)) -> ((a,b),c))

type instance I (,) = ()

instance Tensor' (,) where
  lambda = dimap (\ ~(_,a) -> a) ((,)())
  rho    = dimap (\ ~(a,_) -> a) (\a -> (a,()))

instance Semigroup (,) () where
  mu ((),()) = ()

instance Monoid' (,) () where
  eta _ = id

instance Cosemigroup (,) a where
  delta a = (a,a)

instance Comonoid' (,) a where
  epsilon _ _ = ()

--------------------------------------------------------------------------------
-- * Either and Void
--------------------------------------------------------------------------------

instance Functor Either where
  type Dom Either = (->)
  type Cod Either = Nat (->) (->)
  fmap f = Nat $ \case
    Left a -> Left (f a)
    Right b -> Right b

instance Functor (Either a) where
  type Dom (Either a) = (->)
  type Cod (Either a) = (->)
  fmap f = \case
    Left a -> Left a
    Right b -> Right (f b)

instance Semitensor Either where
  associate = dimap hither yon where
    hither (Left (Left a))  = Left a
    hither (Left (Right b)) = Right (Left b)
    hither (Right c)        = Right (Right c)
    yon (Left a)            = Left (Left a)
    yon (Right (Left b))    = Left (Right b)
    yon (Right (Right c))   = Right c

type instance I Either = Void

instance Tensor' Either where
  lambda = dimap (\(Right a) -> a) Right
  rho = dimap (\(Left a) -> a) Left

instance Semigroup (,) Void where
  mu (a,_) = a

instance Semigroup Either Void where
  mu (Left a)  = a
  mu (Right b) = b

instance Monoid' Either Void where
  eta _ = absurd

instance Cosemigroup Either Void  where
  delta = absurd

instance Comonoid' Either Void where
  epsilon _ = id

--------------------------------------------------------------------------------
-- * The Empty category
--------------------------------------------------------------------------------

data NO = No

-- the functor from the empty category to every category
type No = (Any 'No :: (i -> i -> *) -> Void -> i)

-- thee empty category
data Empty (a :: Void) (b :: Void)

instance Category' c => Functor (No c) where
  type Dom (No c) = Empty
  type Cod (No c) = c
  fmap f = case f of {}

instance Functor Empty where
  type Dom Empty = Op Empty
  type Cod Empty = Nat Empty (->)
  fmap f = case f of {}


instance No (:-) a => Functor (Empty a) where
  type Dom (Empty a) = Empty
  type Cod (Empty a) = (->)
  fmap f = case f of {}

instance Category' Empty where
  type Ob Empty = No (:-)
  id = undefined -- no
  f . _ = case f of {}
  observe f = case f of {}

instance (No (:-) a, No (:-) b) => Equivalent Empty a b where
  equivalent = undefined -- no
  equivSym = Dict

--------------------------------------------------------------------------------
-- * The Unit category
--------------------------------------------------------------------------------

data Unit a b = Unit

instance Functor Unit where
  type Dom Unit = Op Unit
  type Cod Unit = Nat Unit (->)
  fmap _ = Nat $ \_ -> Unit

instance Functor (Unit a) where
  type Dom (Unit a) = Unit
  type Cod (Unit a) = (->)
  fmap _ _ = Unit

instance Category' Unit where
  type Ob Unit = Vacuous Unit
  id = Unit
  Unit . Unit = Unit
  observe _ = Dict

instance Equivalent Unit a b where
  equivalent = Unit
  equivSym = Dict

instance FullyFaithful Unit where
  unfmap _ = Op Unit

instance FullyFaithful (Unit a) where
  unfmap _ = Unit

--------------------------------------------------------------------------------
-- * Coproducts
--------------------------------------------------------------------------------

data Coproduct (c :: i -> i -> *) (d :: j -> j -> *) (a :: Either i j) (b :: Either i j) where
  Inl :: c x y -> Coproduct c d (Left x) (Left y)
  Inr :: d x y -> Coproduct c d (Right x) (Right y)

class CoproductOb (p :: i -> i -> *) (q :: j -> j -> *) (a :: Either i j) where
  side :: Endo (Coproduct p q) a -> (forall x. (a ~ Left x, Ob p x) => r) -> (forall y. (a ~ Right y, Ob q y) => r) -> r
  coproductId :: Endo (Coproduct p q) a

instance (Category p, Ob p x) => CoproductOb (p :: i -> i -> *) (q :: j -> j -> *) (Left x :: Either i j) where
  side _ r _ = r
  coproductId = Inl id

instance (Category q, Ob q y) => CoproductOb (p :: i -> i -> *) (q :: j -> j -> *) (Right y :: Either i j) where
  side _ _ r = r
  coproductId = Inr id

instance (Category p, Category q) => Functor (Coproduct p q) where
  type Dom (Coproduct p q) = Op (Coproduct p q)
  type Cod (Coproduct p q) = Nat (Coproduct p q) (->)
  fmap (Op f) = Nat (. f)

instance (Category p, Category q) => Functor (Coproduct p q a) where
  type Dom (Coproduct p q a) = Coproduct p q
  type Cod (Coproduct p q a) = (->)
  fmap = (.)

instance (Category p, Category q) => Category' (Coproduct p q) where
  type Ob (Coproduct p q) = CoproductOb p q
  id = coproductId
  observe (Inl f) = case observe f of
    Dict -> Dict
  observe (Inr f) = case observe f of
    Dict -> Dict
  Inl f . Inl g = Inl (f . g)
  Inr f . Inr g = Inr (f . g)
  _ . _ = error "Type error"

--------------------------------------------------------------------------------
-- * Get (Lens)
--------------------------------------------------------------------------------

newtype Get (c :: i -> i -> *) (r :: i) (a :: i) (b :: i) = Get { runGet :: c a r }

_Get :: Iso (->) (->) (->) (Get c r a b) (Get c r' a' b') (c a r) (c a' r')
_Get = dimap runGet Get

instance Category c => Functor (Get c) where
  type Dom (Get c) = c
  type Cod (Get c) = Nat (Op c) (Nat c (->))
  fmap = fmap' where
    fmap' :: c a b -> Nat (Op c) (Nat c (->)) (Get c a) (Get c b)
    fmap' f = case observe f of
      Dict -> Nat $ Nat $ _Get (f .)

instance (Category c, Ob c r) => Functor (Get c r) where
  type Dom (Get c r) = Op c
  type Cod (Get c r) = Nat c (->)
  fmap f = case observe f of
    Dict -> Nat $ _Get $ (. unop f)

instance (Category c, Ob c r, Ob c a) => Functor (Get c r a) where
  type Dom (Get c r a) = c
  type Cod (Get c r a) = (->)
  fmap _ = _Get id

get :: (Category c, Ob c a) => (Get c a a a -> Get c a s s) -> c s a
get l = runGet $ l (Get id)

--------------------------------------------------------------------------------
-- * Beget (Lens)
--------------------------------------------------------------------------------

newtype Beget (c :: i -> i -> *) (r :: i) (a :: i) (b :: i) = Beget { runBeget :: c r b }

_Beget :: Iso (->) (->) (->) (Beget c r a b) (Beget c r' a' b') (c r b) (c r' b')
_Beget = dimap runBeget Beget

instance Category c => Functor (Beget c) where
  type Dom (Beget c) = Op c
  type Cod (Beget c) = Nat (Op c) (Nat c (->))
  fmap = fmap' where
    fmap' :: Op c a b -> Nat (Op c) (Nat c (->)) (Beget c a) (Beget c b)
    fmap' f = case observe f of
      Dict -> Nat $ Nat $ _Beget (. op f)

instance (Category c, Ob c r) => Functor (Beget c r) where
  type Dom (Beget c r) = Op c
  type Cod (Beget c r) = Nat c (->)
  fmap f = case observe f of
    Dict -> Nat $ _Beget id

instance (Category c, Ob c r, Ob c a) => Functor (Beget c r a) where
  type Dom (Beget c r a) = c
  type Cod (Beget c r a) = (->)
  fmap f = _Beget (f .)

beget :: (Category c, Ob c b) => (Beget c b b b -> Beget c b t t) -> c b t
beget l = runBeget $ l (Beget id)

(#) :: (Beget (->) b b b -> Beget (->) b t t) -> b -> t
(#) = beget

--------------------------------------------------------------------------------
-- * Compose
--------------------------------------------------------------------------------

data COMPOSE = Compose
type Compose = (Any 'Compose :: (i -> i -> *) -> (j -> j -> *) -> (k -> k -> *) -> (j -> k) -> (i -> j) -> i -> k)

class Category e => Composed (e :: k -> k -> *) where
  _Compose :: (FunctorOf d e f, FunctorOf d e f', FunctorOf c d g, FunctorOf c d g') => Iso
    e e (->)
    (Compose c d e f g a) (Compose c d e f' g' a')
    (f (g a))             (f' (g' a'))

instance Composed (->) where
  _Compose = unsafeCoerce

instance Composed (:-) where
  _Compose = unsafeCoerce

instance (Category c, Composed d) => Composed (Nat c d) where
  _Compose = unsafeCoerce -- really evil, like super-villain evil

instance (Category c, Category d, Category e) => Class (f (g a)) (Compose c d e f g a) where cls = unsafeCoerceConstraint
instance (Category c, Category d, Category e) => f (g a) :=> Compose c d e f g a where ins = unsafeCoerceConstraint

instance (Category c, Category d, Composed e) => Functor (Compose c d e) where
  type Dom (Compose c d e) = Nat d e
  type Cod (Compose c d e) = Nat (Nat c d) (Nat c e)
  fmap = fmap' where
    fmap' :: Nat d e a b -> Nat (Nat c d) (Nat c e) (Compose c d e a) (Compose c d e b)
    fmap' n@Nat{} = nat $ \g -> nat $ \a -> _Compose $ n ! g ! a

instance (Category c, Category d, Composed e, Functor f, e ~ Cod f, d ~ Dom f) => Functor (Compose c d e f) where
  type Dom (Compose c d e f) = Nat c d
  type Cod (Compose c d e f) = Nat c e
  fmap (Nat f) = Nat $ _Compose $ fmap f

instance (Category c, Category d, Composed e, Functor f, Functor g, e ~ Cod f, d ~ Cod g, d ~ Dom f, c ~ Dom g) => Functor (Compose c d e f g) where
  type Dom (Compose c d e f g) = c
  type Cod (Compose c d e f g) = e
  fmap f = _Compose $ fmap $ fmap f

instance (Composed c, c ~ c', c' ~ c'') => Semitensor (Compose c c' c'' :: (i -> i) -> (i -> i) -> (i -> i)) where
  associate = associateCompose

data ID = Id
type Id = (Any 'Id :: (i -> i -> *) -> i -> i)

class Category c => Identified (c :: i -> i -> *) where
  _Id :: Iso c c (->) (Id c a) (Id c a') a a'

instance Identified (->) where
  _Id = unsafeCoerce

instance Identified (:-) where
  _Id = unsafeCoerce

instance (Category c, Identified d) => Identified (Nat c d) where
  _Id = unsafeCoerce

instance Category c => Class a (Id c a) where cls = unsafeCoerceConstraint
instance Category c => a :=> Id c a where ins = unsafeCoerceConstraint

instance Identified c => Functor (Id c) where
  type Dom (Id c) = c
  type Cod (Id c) = c
  fmap = _Id

type instance I (Compose c c c) = Id c

instance (Identified c, Composed c) => Semigroup (Compose c c c) (Id c) where
  mu = dimap (get lambda) id id

instance (Identified c, Composed c) => Monoid' (Compose c c c) (Id c) where
  eta _ = Nat $ _Id id

instance (Identified c, Composed c) => Cosemigroup (Compose c c c) (Id c) where
  delta = dimap id (beget lambda) id

instance (Identified c, Composed c) => Comonoid' (Compose c c c) (Id c) where
  epsilon _ = Nat $ _Id id

instance (Identified c, Composed c) => Tensor' (Compose c c c :: (i -> i) -> (i -> i) -> (i -> i)) where
  lambda = lambdaCompose
  rho = rhoCompose

associateCompose :: forall b c d e f g h f' g' h'.
   ( Category b, Category c, Composed d, Composed e
   , FunctorOf d e f, FunctorOf c d g, FunctorOf b c h
   , FunctorOf d e f', FunctorOf c d g', FunctorOf b c h'
   ) => Iso (Nat b e) (Nat b e) (->)
  (Compose b c e (Compose c d e f g) h) (Compose b c e (Compose c d e f' g') h')
  (Compose b d e f (Compose b c d g h)) (Compose b d e f' (Compose b c d g' h'))
associateCompose = dimap hither yon where
  hither = nat $ \a -> case obOf (id :: NatId f) $ (id :: NatId g) ! (id :: NatId h) ! a of
    Dict -> case obOf (id :: NatId f) $ (id :: NatId (Compose b c d g h)) ! a of
      Dict -> case obOf (id :: NatId (Compose c d e f g)) $ (id :: NatId h) ! a of
        Dict -> beget _Compose . fmap (beget _Compose) . get _Compose . get _Compose
  yon = nat $ \a -> case obOf (id :: NatId f') $ (id :: NatId g') ! (id :: NatId h') ! a of
    Dict -> case obOf (id :: NatId f') $ (id :: NatId (Compose b c d g' h')) ! a of
      Dict -> case obOf (id :: NatId (Compose c d e f' g')) $ (id :: NatId h') ! a of
        Dict -> beget _Compose . beget _Compose . fmap (get _Compose) . get _Compose

lambdaCompose :: forall a a' c. (Identified c, Composed c, Ob (Nat c c) a, Ob (Nat c c) a')
              => Iso (Nat c c) (Nat c c) (->) (Compose c c c (Id c) a) (Compose c c c (Id c) a') a a'
lambdaCompose = dimap hither yon where
  hither = nat $ \z -> case obOf (id :: NatId (Id c)) $ (id :: NatId a) ! z of
    Dict -> get _Id . get _Compose
  yon = nat $ \z -> case obOf (id :: NatId (Id c)) $ (id :: NatId a') ! z of
    Dict -> beget _Compose . beget _Id

rhoCompose :: forall a a' c. (Identified c, Composed c, Ob (Nat c c) a, Ob (Nat c c) a')
           => Iso (Nat c c) (Nat c c) (->) (Compose c c c a (Id c)) (Compose c c c a' (Id c)) a a'
rhoCompose = dimap hither yon where
  hither = nat $ \z -> case obOf (id :: NatId a) $ (id :: NatId (Id c)) ! z of
    Dict -> fmap (get _Id) . get _Compose
  yon = nat $ \z -> case obOf (id :: NatId a') $ (id :: NatId (Id c)) ! z of
    Dict -> beget _Compose . fmap (beget _Id)

--------------------------------------------------------------------------------
-- ** Monads
--------------------------------------------------------------------------------

class (Functor m, Dom m ~ Cod m, Monoid (Compose (Dom m) (Dom m) (Dom m)) m, Identified (Dom m), Composed (Dom m)) => Monad m where
  return :: Ob (Dom m) a => Dom m a (m a)
  return = runNat (eta (id :: NatId (Compose (Dom m) (Dom m) (Dom m)))) . beget _Id
  bind :: forall a b. Ob (Dom m) b => Dom m a (m b) -> Dom m (m a) (m b)
  bind f = case observe f of
    Dict -> case obOf (id :: NatId m) (id :: Endo (Cod m) (m b)) of
      Dict -> runNat mu . beget _Compose . fmap f
instance (Functor m, Dom m ~ Cod m, Monoid (Compose (Dom m) (Dom m) (Dom m)) m, Identified (Dom m), Composed (Dom m)) => Monad m

--------------------------------------------------------------------------------
-- * Prelude
--------------------------------------------------------------------------------

newtype PreludeFunctor f a = PF { runPF :: f a }

_PreludeFunctor :: Iso (->) (->) (->) (PreludeFunctor f a) (PreludeFunctor f' a') (f a) (f' a')
_PreludeFunctor = dimap runPF PF

instance Prelude.Functor f => Functor (PreludeFunctor f) where
  type Dom (PreludeFunctor f) = (->)
  type Cod (PreludeFunctor f) = (->)
  fmap = _PreludeFunctor . Prelude.fmap

instance (Prelude.Functor m, Prelude.Monad m) => Semigroup (Compose (->) (->) (->)) (PreludeFunctor m) where
   mu = Nat $ _PreludeFunctor (Prelude.>>= runPF) . get _Compose
instance (Prelude.Functor m, Prelude.Monad m) => Monoid' (Compose (->) (->) (->)) (PreludeFunctor m) where
  eta _ = Nat $ PF . Prelude.return . get _Id

--------------------------------------------------------------------------------
-- * Coercions
--------------------------------------------------------------------------------

class Category p => Equivalent (p :: i -> i -> *) (a :: i) (b :: i) where
  equivalent :: p a b
  equivSym :: Dict (Equivalent p b a)

instance Class (Category p) (Equivalent p a b) where cls = Sub Dict

instance Coercible a b :=> Equivalent (->) a b where ins = Sub Dict

instance Coercible a b => Equivalent (->) a b where
  equivalent = coerce
  equivSym = case Coercion.sym (Coercion :: Coercion a b) of
    Coercion -> Dict

--------------------------------------------------------------------------------
-- * Normal Forms
--------------------------------------------------------------------------------

type family NF (p :: i -> i -> *) (a :: i) :: i

_NF :: (Equivalent p (NF p a) a, Equivalent q b (NF q b)) => Iso p q (->) (NF p a) (NF q b) a b
_NF = dimap equivalent equivalent

--------------------------------------------------------------------------------
-- * Product of Categories
--------------------------------------------------------------------------------

-- TODO: do this as a product of profunctors instead?
data Product (p :: i -> i -> *) (q :: j -> j -> *) (a :: (i, j)) (b :: (i, j)) =
  Product (p (Fst a) (Fst b)) (q (Snd a) (Snd b))

type family Fst (p :: (i,j)) :: i
type instance Fst '(a,b) = a

type family Snd (q :: (i,j)) :: j
type instance Snd '(a,b) = b

class    (Ob p (Fst a), Ob q (Snd a)) => ProductOb (p :: i -> i -> *) (q :: j -> j -> *) (a :: (i,j))
instance (Ob p (Fst a), Ob q (Snd a)) => ProductOb (p :: i -> i -> *) (q :: j -> j -> *) (a :: (i,j))

instance (Category p, Category q) => Functor (Product p q) where
  type Dom (Product p q) = Op (Product (Opd p) (Opd q))
  type Cod (Product p q) = Nat (Product (Dom2 p) (Dom2 q)) (->)
  fmap f = case observe f of
    Dict -> Nat (. unop f)

instance (Category p, Category q, ProductOb p q a) => Functor (Product p q a) where
  type Dom (Product p q a) = Product (Dom2 p) (Dom2 q)
  type Cod (Product p q a) = (->)
  fmap = (.)

instance (Category p, Category q) => Category' (Product p q) where
  type Ob (Product p q) = ProductOb p q
  id = Product id id
  Product f f' . Product g g' = Product (f . g) (f' . g')
  observe (Product f g) = case observe f of
    Dict -> case observe g of
      Dict -> Dict

type instance NF (Product (p :: i -> i -> *) (q :: j -> j -> *)) (a :: (i,j)) = '(NF p (Fst a), NF q (Snd a))

instance
  ( Ob p (Fst a), Ob p (Fst b), Equivalent p (Fst a) (Fst b)
  , Ob q (Snd a), Ob q (Snd b), Equivalent q (Snd a) (Snd b)
  ) => Equivalent (Product p q) a b where

  equivalent = Product equivalent equivalent

  equivSym = case equivSym :: Dict (Equivalent p (Fst b) (Fst a)) of
    Dict -> case equivSym :: Dict (Equivalent q (Snd b) (Snd a)) of
      Dict -> Dict

--------------------------------------------------------------------------------
-- * Profunctor Composition
--------------------------------------------------------------------------------

type Prof c d = Nat (Op c) (Nat d (->))

class    (Bifunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ (->)) => ProfunctorOf p q f
instance (Bifunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ (->)) => ProfunctorOf p q f

data Procompose (c :: i -> i -> *) (d :: j -> j -> *) (e :: k -> k -> *)
                (p :: j -> k -> *) (q :: i -> j -> *) (a :: i) (b :: k) where
  Procompose :: Ob d x => p x b -> q a x -> Procompose c d e p q a b

instance (Category c, Category d, Category e) => Functor (Procompose c d e) where
  type Dom (Procompose c d e) = Prof d e
  type Cod (Procompose c d e) = Nat (Prof c d) (Prof c e)
  fmap = fmap' where
    fmap' :: Prof d e a b -> Nat (Prof c d) (Prof c e) (Procompose c d e a) (Procompose c d e b)
    fmap' (Nat n) = Nat $ Nat $ Nat $ \(Procompose p q) -> Procompose (runNat n p) q

instance (Category c, Category d, Category e, ProfunctorOf d e p) => Functor (Procompose c d e p) where
  type Dom (Procompose c d e p) = Prof c d
  type Cod (Procompose c d e p) = Prof c e
  fmap = fmap' where
    fmap' :: Prof c d a b -> Prof c e (Procompose c d e p a) (Procompose c d e p b)
    fmap' (Nat n) = Nat $ Nat $ \(Procompose p q) -> Procompose p (runNat n q)

instance (Category c, Category d, Category e, ProfunctorOf d e p, ProfunctorOf c d q) => Functor (Procompose c d e p q) where
  type Dom (Procompose c d e p q) = Op c
  type Cod (Procompose c d e p q) = Nat e (->)
  fmap f = case observe f of
    Dict -> Nat $ \(Procompose p q) -> Procompose p (runNat (fmap f) q)

instance (Category c, Category d, Category e, ProfunctorOf d e p, ProfunctorOf c d q, Ob c a) => Functor (Procompose c d e p q a) where
  type Dom (Procompose c d e p q a) = e
  type Cod (Procompose c d e p q a) = (->)
  fmap f (Procompose p q) = Procompose (fmap1 f p) q

-- TODO

{-
associateProcompose :: Iso (Prof c e) (Prof c e) (->)
  (Procompose c d f (Procompose d e f p q) r) (Procompose c' d' f' (Procompose d' e' f' p' q') r')
  (Procompose c e f p (Procompose c d e q r)) (Procompose c' e' f' p' (Procompose c' d' e' q' r'))
associateProcompose = dimap
  (Nat $ Nat $ \ (Procompose (Procompose a b) c) -> Procompose a (Procompose b c))
  (Nat $ Nat $ \ (Procompose a (Procompose b c)) -> Procompose (Procompose a b) c)
-}

--------------------------------------------------------------------------------
-- * Totality
--------------------------------------------------------------------------------

total :: forall a b p. (Category p, Ob p a) => Nat (Op p) (->) (Op p a) (Op p b) -> p a b
total (Nat n) = unop (n (id :: Endo (Op p) a))

--------------------------------------------------------------------------------
-- * Adjunctions
--------------------------------------------------------------------------------

class (Functor f, Functor g, Dom f ~ Cod g, Cod g ~ Dom f) => (f :: j -> i) -| (g :: i -> j) | f -> g, g -> f where
  adj :: Iso (->) (->) (->) (Cod f (f a) b) (Cod f (f a') b') (Cod g a (g b)) (Cod g a' (g b'))

instance (,) e -| (->) e where
  adj = dimap (. swap) (. swap) . curried

swap :: (a,b) -> (b, a)
swap (a,b) = (b,a)

class (Bifunctor p, Bifunctor q) => Curried (p :: k -> i -> j) (q :: i -> j -> k) | p -> q, q -> p where
  curried :: Iso (->) (->) (->)
    (Dom2 p (p a b) c) (Dom2 p (p a' b') c')
    (Dom2 q a (q b c)) (Dom2 q a' (q b' c'))

instance Curried (,) (->) where
  curried = dimap Prelude.curry Prelude.uncurry

--------------------------------------------------------------------------------
-- * Limits
--------------------------------------------------------------------------------

{-
data LIM = Lim
type Lim = (Any 'Lim :: (i -> i -> *) -> (j -> j -> *) -> (i -> j) -> j)

data CONST = Const
type Const = (Any 'Const :: (i -> i -> *) -> (j -> j -> *) -> j -> i -> j)

class Category c => Complete c where
  _Const :: Iso c c c (Const j c a b) (Const j' c a' b') a a'
  ..

instance (Category j, Complete c) => Const j c -| Lim j c where
  adj = ..

instance (Category j, Complete c) => Functor (Const j c) where
  type Dom (Const j c a) = c
  type Cod (Const j c a) = Nat j c

instance (Category j, Complete c, Ob c a) => Functor (Const j c a) where
  type Dom (Const j c a) = j
  type Cod (Const j c a) = c

instance (Category j, Complete c) => Functor (Lim j c) where
  type Dom (Lim j c) = Nat j c
  type Cod (Lim j c) = c
-}

--------------------------------------------------------------------------------
-- * Diagonal
--------------------------------------------------------------------------------

data DIAG = Diag
type Diag = (Any 'Diag :: (i -> i -> *) -> i -> (i,i))

type instance Fst (Diag c a) = a
type instance Snd (Diag c a) = a

instance Category c => Functor (Diag c) where
  type Dom (Diag c) = c
  type Cod (Diag c) = Product c c
  fmap f = Product f f

--------------------------------------------------------------------------------
-- * Day Convolution
--------------------------------------------------------------------------------

class FunctorOf c (->) f => CopresheafOf c f
instance FunctorOf c (->) f => CopresheafOf c f

data Day (t :: i -> i -> i) (f :: i -> *) (g :: i -> *) (a :: i) where
  Day :: (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, Ob c x, Ob c y)
      => c (t x y) a -> f x -> g y -> Day t f g a

--Day convolution of copresheaves is a copresheaf

instance (Dom t ~ c, CopresheafOf c f, CopresheafOf c g) => Functor (Day t f g) where
  type Dom (Day t f g) = Dom t
  type Cod (Day t f g) = (->)
  fmap c' (Day c fx gy) = Day (c' . c) fx gy

--Day convolution is a bifunctor of copresheaves

instance (Dom t ~ c, CopresheafOf c f) => Functor (Day t f) where
  type Dom (Day t f) = Copresheaves (Dom t)
  type Cod (Day t f) = Copresheaves (Dom t)
  fmap = fmap' where
    fmap' :: Copresheaves c g g' -> Copresheaves c (Day t f g) (Day t f g')
    fmap' (Nat natg) = Nat $ \(Day c fx gy) -> Day c fx (natg gy)

instance (Dom t ~ c, Category c) => Functor (Day t) where
  type Dom (Day t) = Copresheaves (Dom t)
  type Cod (Day t) = Nat (Copresheaves (Dom t)) (Copresheaves (Dom t))
  fmap = fmap' where
    fmap' :: Copresheaves c f f' -> Nat (Copresheaves c) (Copresheaves c) (Day t f) (Day t f')
    fmap' (Nat natf) = Nat $ Nat $ \(Day c fx gy) -> Day c (natf fx) gy

--Day convolution on a monoidal category is associative making it a Semitensor

data Day3L (t :: i -> i -> i) (f :: i -> *) (g :: i -> *) (h :: i -> *) (a :: i) where
  Day3L :: (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, CopresheafOf c h, Ob c x, Ob c y, Ob c z)
         => c (t (t x y) z) a -> f x -> g y -> h z -> Day3L t f g h a

data Day3R (t :: i -> i -> i) (f :: i -> *) (g :: i -> *) (h :: i -> *) (a :: i) where
  Day3R :: (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, CopresheafOf c h, Ob c x, Ob c y, Ob c z)
         => c (t x (t y z)) a -> f x -> g y -> h z -> Day3R t f g h a

instance (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, CopresheafOf c h) => Functor (Day3L t f g h) where
  type Dom (Day3L t f g h) = Dom t
  type Cod (Day3L t f g h) = (->)
  fmap c' (Day3L c fx gy hz) = Day3L (c' . c) fx gy hz

instance (Dom t ~ c, CopresheafOf c f, CopresheafOf c g, CopresheafOf c h) => Functor (Day3R t f g h) where
  type Dom (Day3R t f g h) = Dom t
  type Cod (Day3R t f g h) = (->)
  fmap c' (Day3R c fx gy hz) = Day3R (c' . c) fx gy hz

--Thanks to Shachaf for help with the semitensorClosed constraint
semitensorClosed :: forall c t x y. (Semitensor t, Category c, Dom t ~ c, Ob c x, Ob c y) => Dict (Ob c (t x y))
semitensorClosed = case ob :: Ob c x :- FunctorOf c c (t x) of
  Sub Dict -> case ob :: Ob c y :- Ob c (t x y) of
    Sub Dict -> Dict

day3 :: (Semitensor t, Dom t ~ c, Category c
     , CopresheafOf c f, CopresheafOf c g, CopresheafOf c h
     , CopresheafOf c f', CopresheafOf c g', CopresheafOf c h'
     ) => Iso (Copresheaves c) (Copresheaves c) (->)
         (Day3L t f g h) (Day3L t f' g' h')
         (Day3R t f g h) (Day3R t f' g' h')
day3 = dimap (Nat hither) (Nat yon)
  where
    hither :: (Semitensor t, Dom t ~ c, Category c) => Day3L t f g h a -> Day3R t f g h a
    hither (Day3L (c :: c (t (t x y) z) a) fx gy hz) = case semitensorClosed :: Dict (Ob c (t y z)) of
      Dict -> case semitensorClosed :: Dict (Ob c (t x (t y z))) of
        Dict -> Day3R (c . beget associate) fx gy hz
    yon :: (Semitensor t, Dom t ~ c, Category c) => Day3R t f g h a -> Day3L t f g h a
    yon (Day3R (c :: c (t x (t y z)) a) fx gy hz) = case semitensorClosed :: Dict (Ob c (t y z)) of
      Dict -> case semitensorClosed :: Dict (Ob c (t x (t y z))) of
        Dict -> Day3L (c . get associate) fx gy hz

dayL :: (Semitensor t, Dom t ~ c, Category c
     , CopresheafOf c f, CopresheafOf c g, CopresheafOf c h
     , CopresheafOf c f', CopresheafOf c g', CopresheafOf c h'
     ) => Iso (Copresheaves c) (Copresheaves c) (->)
         (Day t (Day t f g) h) (Day t (Day t f' g') h')
         (Day3L t f g h)       (Day3L t f' g' h')
dayL = dimap (Nat hither) (Nat yon)
  where
    hither :: (Semitensor t, Dom t ~ c, Category c) => Day t (Day t f g) h a -> Day3L t f g h a
    hither (Day c' (Day c fx gy) hz) = Day3L (c' . runNat (fmap c)) fx gy hz
    yon :: (Semitensor t, Dom t ~ c, Category c) => Day3L t f g h a -> Day t (Day t f g) h a
    yon (Day3L (c :: c (t (t x y) z) a) fx gy hz) = case semitensorClosed :: Dict (Ob c (t x y)) of
      Dict -> Day c (Day id fx gy) hz

dayR :: (Semitensor t, Dom t ~ c, Category c
     , CopresheafOf c f, CopresheafOf c g, CopresheafOf c h
     , CopresheafOf c f', CopresheafOf c g', CopresheafOf c h'
     ) => Iso (Copresheaves c) (Copresheaves c) (->)
         (Day3R t f g h)       (Day3R t f' g' h')
         (Day t f (Day t g h)) (Day t f' (Day t g' h'))
dayR = dimap (Nat hither) (Nat yon)
  where
    hither :: (Semitensor t, Dom t ~ c, Category c) => Day3R t f g h a -> Day t f (Day t g h) a
    hither (Day3R (c :: c (t x (t y z)) a) fx gy hz) = case semitensorClosed :: Dict (Ob c (t y z)) of
      Dict -> Day c fx (Day id gy hz)
    yon :: (Semitensor t, Dom t ~ c, Category c) => Day t f (Day t g h) a -> Day3R t f g h a
    yon (Day c' fx (Day c gy hz)) = Day3R (c' . fmap1 c) fx gy hz

instance (Semitensor t, Category (Dom t)) => Semitensor (Day t)
  where associate = dayL . day3 . dayR