{-# LANGUAGE KindSignatures, PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, NoImplicitPrelude, TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables, DataKinds, AllowAmbiguousTypes, LambdaCase, DefaultSignatures #-}
module Univariant where

import Data.Constraint (Constraint, (:-)(Sub), Dict(..), (\\), Class(cls), (:=>)(ins))
import qualified Data.Constraint as Constraint
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Data.Proxy (Proxy(..))
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion
import Data.Void
import GHC.Prim (Any, Coercible, coerce)
import Prelude (($),undefined,Either(..))
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
  -- Op (Product p q) = Product (Op p) (Op q)
  Op p = Yoneda p

-- | Side-conditions moved to 'Functor' to work around GHC bug #9200.
--
-- You should produce instances of 'Category'' and consume instances of 'Category'.
--
-- All of our categories are "locally small", and we "curry" the Hom-functor
-- as a functor to the category of copresheaves.
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

--------------------------------------------------------------------------------
-- * Functors
--------------------------------------------------------------------------------

-- | Side-conditions moved to 'Functor' to work around GHC bug #9200.
--
-- You should produce instances of 'Functor'' and consume instances of 'Functor'.
class Functor' (f :: i -> j)  where
  type Dom f :: i -> i -> *
  type Cod f :: j -> j -> *
  fmap :: Dom f a b -> Cod f (f a) (f b)

class    (Functor' f, Category' (Dom f), Category' (Cod f)) => Functor f
instance (Functor' f, Category' (Dom f), Category' (Cod f)) => Functor f

ob :: forall f a. Functor f => Ob (Dom f) a :- Ob (Cod f) (f a)
ob = Sub $ case observe (fmap (id :: Dom f a a) :: Cod f (f a) (f a)) of
  Dict -> Dict

--------------------------------------------------------------------------------
-- * Bifunctors
--------------------------------------------------------------------------------

type family NatDom (f :: (i -> j) -> (i -> j) -> *) :: (i -> i -> *) where NatDom (Nat p q) = p
type family NatCod (f :: (i -> j) -> (i -> j) -> *) :: (j -> j -> *) where NatCod (Nat p q) = q

type Dom2 (p :: i -> j -> k) = (NatDom (Cod p :: (j -> k) -> (j -> k) -> *) :: j -> j -> *)
type Cod2 (p :: i -> j -> k) = (NatCod (Cod p :: (j -> k) -> (j -> k) -> *) :: k -> k -> *)

class (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)
instance  (Functor p, Cod p ~ Nat (Dom2 p) (Cod2 p), Category' (Dom2 p), Category' (Cod2 p)) => Bifunctor (p :: i -> j -> k)

fmap1 :: forall p a b c. (Bifunctor p, Ob (Dom p) c) => Dom2 p a b -> Cod2 p (p c a) (p c b)
fmap1 f = case ob :: Ob (Dom p) c :- FunctorOf (Dom2 p) (Cod2 p) (p c) of
  Sub Dict -> fmap f where

bimap :: Bifunctor p => Dom p a b -> Dom2 p c d -> Cod2 p (p a c) (p b d)
bimap f g = case observe f of
  Dict -> case observe g of
    Dict -> runNat (fmap f) . fmap1 g

--------------------------------------------------------------------------------
-- * Contravariance
--------------------------------------------------------------------------------

type Opd f = Op (Dom f)

class (Dom p ~ Op (Opd p)) => Contra p
instance (Dom p ~ Op (Opd p)) => Contra p

class (Contra f, Functor f) => Contravariant f
instance (Contra f, Functor f) => Contravariant f

contramap :: Contravariant f => Opd f b a -> Cod f (f a) (f b)
contramap = fmap . unop

--------------------------------------------------------------------------------
-- * Profunctors
--------------------------------------------------------------------------------

-- | E-Enriched profunctors f : C -/-> D are represented by a functor of the form:
--
-- C^op -> [ D, E ]
--
-- The variance here matches Haskell's order, which means that the contravariant
-- argument comes first!
class (Contra f, Bifunctor f) => Profunctor f
instance (Contra f, Bifunctor f) => Profunctor f

dimap :: Profunctor p => Opd p b a -> Dom2 p c d -> Cod2 p (p a c) (p b d)
dimap = bimap . unop

type Iso
  (c :: i -> i -> *) (d :: j -> j -> *) (e :: k -> k -> *)
  (s :: i) (t :: j) (a :: i) (b :: j) = forall (p :: i -> j -> k).
  (Profunctor p, Dom p ~ Op c, Dom2 p ~ d, Cod2 p ~ e) => e (p a b) (p s t)

--------------------------------------------------------------------------------
-- * Categories (Part 2)
--------------------------------------------------------------------------------

class    (Category' p, Profunctor p, Dom p ~ Op p, Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->)) => Category'' p
instance (Category' p, Profunctor p, Dom p ~ Op p, Cod p ~ Nat p (->), Dom2 p ~ p, Cod2 p ~ (->)) => Category'' p

-- | The full definition for a (locally-small) category.
class    (Category'' p, Category'' (Op p), p ~ Op (Op p), Ob p ~ Ob (Op p)) => Category p
instance (Category'' p, Category'' (Op p), p ~ Op (Op p), Ob p ~ Ob (Op p)) => Category p

--------------------------------------------------------------------------------
-- * Vacuous
--------------------------------------------------------------------------------

class Vacuous (c :: i -> i -> *) (a :: i)
instance Vacuous c a

instance Functor' Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap f Dict = case f of Sub g -> g

instance (Ob c ~ Vacuous c) => Functor' (Vacuous c) where
  type Dom (Vacuous c) = c
  type Cod (Vacuous c) = (:-)
  fmap _ = Sub Dict

--------------------------------------------------------------------------------
-- * The Category of Constraints
--------------------------------------------------------------------------------

instance Functor' (:-) where
  type Dom (:-) = Op (:-)
  type Cod (:-) = Nat (:-) (->) -- copresheaves
  fmap (Op f) = Nat (. f)

instance Functor' ((:-) b) where
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

--------------------------------------------------------------------------------
-- * Hask
--------------------------------------------------------------------------------

instance Functor' (->) where
  type Dom (->) = Op (->)
  type Cod (->) = Nat (->) (->)
  fmap (Op f) = Nat (. f)

instance Functor' ((->)a) where
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

instance (Category p, Op p ~ Yoneda p) => Functor' (Yoneda p) where
  type Dom (Yoneda p) = p
  type Cod (Yoneda p) = Nat (Yoneda p) (->)
  fmap f = Nat (. Op f)

instance (Category p, Op p ~ Yoneda p) => Functor' (Yoneda p a) where
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

--------------------------------------------------------------------------------
-- * Nat
--------------------------------------------------------------------------------

data Nat (p :: i -> i -> *) (q :: j -> j -> *) (f :: i -> j) (g :: i -> j) where
  Nat :: ( FunctorOf p q f
         , FunctorOf p q g
         ) => {
           runNat :: forall a. Ob p a => q (f a) (g a)
         } -> Nat p q f g

type Copresheaves p = Nat p (->)
type Presheaves p = Nat (Op p) (->)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

instance Functor' (FunctorOf p q) where
  type Dom (FunctorOf p q) = Nat p q
  type Cod (FunctorOf p q) = (:-)
  fmap Nat{} = Sub Dict

instance (Category' p, Category q) => Functor' (Nat p q) where
  type Dom (Nat p q) = Op (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Op f) = Nat (. f)

instance (Category' p, Category q) => Functor' (Nat p q a) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  fmap = (.)

instance (Category' p, Category' q) => Category' (Nat p q) where
   type Ob (Nat p q) = FunctorOf p q
   id = Nat id1 where
     id1 :: forall f x. (Functor' f, Dom f ~ p, Cod f ~ q, Ob p x) => q (f x) (f x)
     id1 = id \\ (ob :: Ob p x :- Ob q (f x))
   observe Nat{} = Dict
   Nat f . Nat g = Nat (f . g)
   unop = getOp

nat :: (Category p ,Category q, FunctorOf p q f, FunctorOf p q g) => (forall a. Ob p a => Proxy a -> q (f a) (g a)) -> Nat p q f g
nat k = Nat (k Proxy)

natDict :: (Category p, Category q) => Dict (Category (Nat p q))
natDict = Dict

natById :: (FunctorOf p q f, FunctorOf p q g) => (forall a. p a a -> q (f a) (g a)) -> Nat p q f g
natById f = Nat (f id)

runNatById :: Nat p q f g -> p a a -> q (f a) (g a)
runNatById (Nat n) f = case observe f of
  Dict -> n

--------------------------------------------------------------------------------
-- * Monoidal Tensors and Monoids
--------------------------------------------------------------------------------

class (Bifunctor p, Dom p ~ Dom2 p, Dom p ~ Cod2 p) => Semitensor p where
  associate :: (Ob (Dom p) a, Ob (Dom p) b, Ob (Dom p) c, Ob (Dom p) a', Ob (Dom p) b', Ob (Dom p) c')
            => Iso (Dom p) (Dom p) (->) (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))

type family I (p :: i -> i -> i) :: i

class Semitensor p => Tensor' p where
  lambda :: Iso (Dom p) (Dom p) (Dom p) (p (I p) a) (p (I p) a') a a'
  rho    :: Iso (Dom p) (Dom p) (Dom p) (p a (I p)) (p a' (I p)) a a'

class (Monoid' p (I p), Tensor' p) => Tensor p
instance (Monoid' p (I p), Tensor' p) => Tensor p

class Semitensor p => Semigroup p m where
  mu :: Dom p (p m m) m

class (Semigroup p m, Tensor' p) => Monoid' p m where
  eta :: Proxy p -> Dom p (I p) m

class (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Monoid' p m) => Monoid p m
instance (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Monoid' p m) => Monoid p m

class Semitensor p => Cosemigroup p w where
  delta :: Dom p w (p w w)

class (Cosemigroup p w, Tensor' p) => Comonoid' p w where
  epsilon :: Proxy p -> Dom p w (I p)

class (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Comonoid' p w) => Comonoid p w
instance (Monoid' p (I p), Comonoid' p (I p), Tensor' p, Comonoid' p w) => Comonoid p w

--------------------------------------------------------------------------------
-- * (&)
--------------------------------------------------------------------------------

class (p, q) => p & q
instance (p, q) => p & q

instance Functor' (&) where
  type Dom (&) = (:-)
  type Cod (&) = Nat (:-) (:-)
  fmap f = Nat $ Sub $ Dict \\ f

instance Functor' ((&) a) where
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

instance Functor' (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat $ \(a,b) -> (f a, b)

instance Functor' ((,) a) where
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

instance Functor' Either where
  type Dom Either = (->)
  type Cod Either = Nat (->) (->)
  fmap f = Nat $ \case
    Left a -> Left (f a)
    Right b -> Right b

instance Functor' (Either a) where
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
-- * Get (Lens)
--------------------------------------------------------------------------------

newtype Get (c :: i -> i -> *) (r :: i) (a :: i) (b :: i) = Get { runGet :: c a r }

_Get :: Iso (->) (->) (->) (Get c r a b) (Get c r' a' b') (c a r) (c a' r')
_Get = dimap runGet Get

instance Category c => Functor' (Get c) where
  type Dom (Get c) = c
  type Cod (Get c) = Nat (Op c) (Nat c (->))
  fmap = fmap'
    where
      fmap' :: c a b -> Nat (Op c) (Nat c (->)) (Get c a) (Get c b)
      fmap' f = case observe f of Dict -> Nat $ Nat $ _Get (f .)

instance (Category c, Ob c r) => Functor' (Get c r) where
  type Dom (Get c r) = Op c
  type Cod (Get c r) = Nat c (->)
  fmap f = case observe f of
    Dict -> Nat $ _Get $ (. unop f)

instance (Category c, Ob c r, Ob c a) => Functor' (Get c r a) where
  type Dom (Get c r a) = c
  type Cod (Get c r a) = (->)
  fmap f = _Get id

get :: (Category c, Ob c a) => (Get c a a a -> Get c a s s) -> c s a
get l = runGet $ l (Get id)

--------------------------------------------------------------------------------
-- * Beget (Lens)
--------------------------------------------------------------------------------

newtype Beget (c :: i -> i -> *) (r :: i) (a :: i) (b :: i) = Beget { runBeget :: c r b }

_Beget :: Iso (->) (->) (->) (Beget c r a b) (Beget c r' a' b') (c r b) (c r' b')
_Beget = dimap runBeget Beget

instance Category c => Functor' (Beget c) where
  type Dom (Beget c) = Op c
  type Cod (Beget c) = Nat (Op c) (Nat c (->))
  -- fmap (Yoneda f) = Nat $ Nat $ _Beget (. f) -- TODO

instance (Category c, Ob c r) => Functor' (Beget c r) where
  type Dom (Beget c r) = Op c
  type Cod (Beget c r) = Nat c (->)
  fmap f = case observe f of
    Dict -> Nat $ _Beget id

instance (Category c, Ob c r, Ob c a) => Functor' (Beget c r a) where
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

instance (Category c, Category d, Composed e) => Functor' (Compose c d e) where
  type Dom (Compose c d e) = Nat d e
  type Cod (Compose c d e) = Nat (Nat c d) (Nat c e)
  fmap n@Nat{} = natById $ \g@Nat{} -> natById $ _Compose . runNatById n . runNatById g

instance (Category c, Category d, Composed e, Functor f, e ~ Cod f, d ~ Dom f) => Functor' (Compose c d e f) where
  type Dom (Compose c d e f) = Nat c d
  type Cod (Compose c d e f) = Nat c e
  fmap (Nat f) = Nat $ _Compose $ fmap f

instance (Category c, Category d, Composed e, Functor f, Functor g, e ~ Cod f, d ~ Cod g, d ~ Dom f, c ~ Dom g) => Functor' (Compose c d e f g) where
  type Dom (Compose c d e f g) = c
  type Cod (Compose c d e f g) = e
  fmap f = _Compose $ fmap $ fmap f

instance (Composed c, c ~ c', c' ~ c'') => Semitensor (Compose c c' c'' :: (i -> i) -> (i -> i) -> (i -> i)) where
  associate = associateCompose

associateCompose :: (Category b, Category c, Composed d, Composed e,
    FunctorOf d e f, FunctorOf c d g, FunctorOf b c h,
    FunctorOf d e f', FunctorOf c d g', FunctorOf b c h')
    => Iso (Nat b e) (Nat b e) (->)
  (Compose b c e (Compose c d e f g) h) (Compose b c e (Compose c d e f' g') h')
  (Compose b d e f (Compose b c d g h)) (Compose b d e f' (Compose b c d g' h'))
associateCompose = dimap (Nat undefined) (Nat undefined) -- TODO
-- associateCompose = dimap (Nat (beget _Compose . fmap (beget _Compose) . get _Compose . get _Compose))
--                          (Nat (beget _Compose . beget _Compose . fmap (get _Compose) . get _Compose))

--------------------------------------------------------------------------------
-- * Coercions
--------------------------------------------------------------------------------

class (Category p, Ob p a, Ob p b) => Equivalent (p :: i -> i -> *) (a :: i) (b :: i) where
  equivalent :: p a b

instance Coercible a b => Equivalent (->) a b where
  equivalent = coerce

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

instance (Category p, Category q) => Functor' (Product p q) where
  -- Yoneda (Product (Op p) (Op q))
  type Dom (Product p q) = Op (Product (Dom p) (Dom q))
  type Cod (Product p q) = Nat (Product (Dom2 p) (Dom2 q)) (->)

instance (Category p, Category q, ProductOb p q a) => Functor' (Product p q a) where
  type Dom (Product p q a) = Product (Dom2 p) (Dom2 q)
  type Cod (Product p q a) = (->)

instance (Category p, Category q) => Category' (Product p q) where
  type Ob (Product p q) = ProductOb p q
  id = Product id id
  Product f f' . Product g g' = Product (f . g) (f' . g')
  observe (Product f g) = case observe f of
    Dict -> case observe g of
      Dict -> Dict

type instance NF (Product (p :: i -> i -> *) (q :: j -> j -> *)) (a :: (i,j)) = '(NF p (Fst a), NF q (Snd a))

{-
instance
  ( Category p, Ob p (Fst a), Ob q (Snd a), Equivalent p (Fst a) (Fst b)
  , Category q, Ob p (Fst b), Ob q (Snd b), Equivalent q (Snd a) (Snd b)
  ) => Equivalent (Product (p :: i -> i -> *) (q :: j -> j -> *) :: (i,j) -> (i,j) -> *) (a :: (i,j)) (b :: (i,j)) where
  -- equivalent = Product equivalent equivalent
-}

--------------------------------------------------------------------------------
-- * Profunctor Composition
--------------------------------------------------------------------------------

type Prof c d e = Nat (Op c) (Nat d e)

class    (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ r) => ProfunctorOf p q r f
instance (Profunctor f, Dom f ~ Op p, Dom2 f ~ q, Cod2 f ~ r) => ProfunctorOf p q r f

-- TODO: strip off f just to get basic unenriched profunctors to work

{-
data PROCOMPOSE = Procompose
type Procompose = (Any 'Procompose :: (i -> i -> l) -> (j -> j -> l) -> (k -> k -> l) -> (l -> l -> l) ->
                                      (j -> k -> l) -> (i -> j -> l) -> i -> k -> l
-}

data Procompose (c :: i -> i -> *) (d :: j -> j -> *) (e :: k -> k -> *) (f :: * -> * -> *)
                (p :: j -> k -> *) (q :: i -> j -> *) (a :: i) (b :: k) where
  Procompose :: p x b -> q a x -> Procompose c d e f p q a b

instance (Category c, Category d, Category e, Category f) => Functor' (Procompose c d e f) where
  type Dom (Procompose c d e f) = Prof d e f
  type Cod (Procompose c d e f) = Nat (Prof c d f) (Prof c e f)
  -- fmap = todo

instance (Category c, Category d, Category e, Category f, ProfunctorOf d e f p) => Functor' (Procompose c d e f p) where
  type Dom (Procompose c d e f p) = Prof c d f
  type Cod (Procompose c d e f p) = Prof c e f
  -- fmap = todo

instance (Category c, Category d, Category e, Category f, ProfunctorOf d e f p, ProfunctorOf c d f q) => Functor' (Procompose c d e f p q) where
  type Dom (Procompose c d e f p q) = Op c
  type Cod (Procompose c d e f p q) = Nat e f
  -- fmap = todo

instance (Category c, Category d, Category e, Category f, ProfunctorOf d e f p, ProfunctorOf c d f q, Ob c a) => Functor' (Procompose c d e f p q a) where
  type Dom (Procompose c d e f p q a) = e
  type Cod (Procompose c d e f p q a) = f
  -- fmap = todo

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
-- * Day Convolution
--------------------------------------------------------------------------------

{-
data DAY = Day
type Day = (Any 'Day :: (i -> i -> *) -> (j -> j -> *) -> (i -> j) -> (i -> j) -> (i -> j))
-}

-- data Day (c :: i -> i -> *) (d :: * -> * -> *) (f :: i -> *) (g :: i -> *) (a :: i) :: * where
--   Day :: forall b

class Category p => Total p where
  total :: Nat (Op p) (->) (Op p a) (Op p b) -> p a b

instance (Category p, Op p ~ Yoneda p) => Total (Yoneda p) where
  total = undefined -- TODO
