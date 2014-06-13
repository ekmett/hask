{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DefaultSignatures #-}

import qualified Control.Arrow as Arrow
import qualified Control.Applicative as Applicative
import Control.Category
import Data.Functor.Identity
import Data.Traversable
import Data.Typeable
import Data.Void
import Prelude hiding (map, id, (.), fst, snd)
import qualified Prelude

-- infixl 4 <$>
-- infixl 4 <*>

-- * Enriched Profunctors
-- p : C^op x D -> E

-- |
-- The signature
--
-- @
-- class (Category c, Category d, Cartesian e) => Profunctor
-- @
--
-- would need GHC trac issue #9200 to be fixed.
class (Category c, Category d, Category e) => Profunctor
    (p :: x -> y -> z)
    (c :: x -> x -> *)
    (d :: y -> y -> *)
    (e :: z -> z -> *)
    | p -> c d e where

  dimap :: c a a' -> d b b' -> e (p a' b) (p a b')

  lmap :: c a a' -> e (p a' b) (p a b)
  lmap f = dimap f id

  rmap :: d b b' -> e (p a b) (p a b')
  rmap = dimap id

instance Profunctor (->) (->) (->) (->) where
  dimap f g h = g . h . f
  -- dimap f g = from _Hom (dimap f g)

-- lens-style isomorphism families in an arbitrary category
type Iso (c :: i -> i -> *) (s :: i) (t :: i) (a :: i) (b :: i) = forall (p :: i -> i -> *). Profunctor p c c (->) => p a b -> p s t

data Exchange c a b s t where
  Exchange :: c s a -> c b t -> Exchange c a b s t

mapping :: Functorial f c c => (Exchange c a b a b -> Exchange c a b s t) -> Iso c (f s) (f t) (f a) (f b)
mapping l = case l (Exchange id id) of
  Exchange csa dbt -> dimap (map csa) (map dbt)

newtype Hom k a b = Hom { runHom :: k a b }

instance Category k => Profunctor (Hom k) k k (->) where
  dimap f g h = Hom $ g . runHom h . f

_Hom :: Iso (->) (Hom k a b) (Hom k' a' b') (k a b) (k' a' b')
_Hom = dimap runHom Hom

-- * Viewing

newtype Forget c r a b = Forget { runForget :: c a r }

instance Category k => Profunctor (Forget k r) k k (->) where
  dimap f _ (Forget ar) = Forget (ar . f)

_Forget :: Iso (->) (Forget c r a b) (Forget c' r' a' b') (c a r) (c' a' r')
_Forget = dimap runForget Forget

view :: Category k => (Forget k a a a -> Forget k a s s) -> k s a
view l = runForget $ l (Forget id)

newtype From p a b s t = From { runFrom :: p t s -> p b a }

_From :: Iso (->) (From p a b s t) (From p' a' b' s' t') (p t s -> p b a) (p' t' s' -> p' b' a')
_From = dimap runFrom From

instance Profunctor p d c (->) => Profunctor (From p a b) c d (->) where
  dimap f g = _From $ lmap (dimap g f)

from :: (From p a b a b -> From p a b s t) -> p t s -> p b a
from l = runFrom $ l $ From id

review :: Category k => (From (Forget k a) s s s s -> From (Forget k a) s s a a) -> k s a
review = view.from

-- * Natural transformations

-- newtype NAT (d :: y -> y -> *) (f :: x -> y) (g :: x -> y) = Nat { runNat :: forall a. d (f a) (g a) }

-- Nat :: (* -> *) -> (* -> *) -> *
newtype Nat (x :: i -> *) (y :: i -> *) = Nat { runNat :: forall (a :: i). x a -> y a }

instance Category Nat where
  id = Nat id
  Nat f . Nat g = Nat (f . g)

instance Profunctor Nat Nat Nat (->) where
  dimap f g = from _Hom (dimap f g)

-- * Lifting bifunctors

newtype Natural (p :: y -> y -> *) (f :: x -> y) (g :: x -> y) (a :: x) = Natural { runNatural :: p (f a) (g a) } -- could be used with Natural (,), Natural Either, Natural (->) to get corresponding entries for Nat

_Natural :: Iso (->) (Natural p f g a) (Natural p' f' g' a') (p (f a) (g a)) (p' (f' a') (g' a'))
_Natural = dimap runNatural Natural

instance Profunctor p (->) (->) (->) => Profunctor (Natural p) Nat Nat Nat where
  dimap (Nat f) (Nat g) = Nat $ _Natural $ dimap f g

class (Category c, Category d) => Functorial f c d | f c -> d, f d -> c where
  map :: c a b -> d (f a) (f b)

instance Functor g => Functorial g (->) (->) where
  map = fmap

instance Functorial (Natural (,) f) Nat Nat where
  map = second

instance Functorial (Natural Either f) Nat Nat where
  map = second

instance Functorial (Natural (->) f) Nat Nat where
  map = rmap

(<$>) :: Functorial f c (->) => c a b -> f a -> f b
(<$>) = map

newtype K b a = K { runK :: b } deriving (Eq,Ord,Show,Read,Typeable)

_K :: Iso (->) (K b a) (K b' a') b b'
_K = dimap runK K

newtype An f a = An (f a) deriving (Eq,Ord,Show,Read,Typeable)

data Procompose (p :: x -> y -> *) (q :: y -> z -> *) (d :: x) (c :: z) where
  Procompose :: p d a -> q a c -> Procompose p q d c

instance (Profunctor p c d (->), Profunctor q d e (->)) => Profunctor (Procompose p q) c e (->) where
  dimap f g (Procompose p q) = Procompose (lmap f p) (rmap g q)

newtype Up (c :: x -> x -> *) (f :: y -> x) (a :: x) (b :: y)  = Up { runUp :: c a (f b) }

_Up :: Iso (->) (Up c f a b) (Up c' f' a' b') (c a (f b)) (c' a' (f' b'))
_Up = dimap runUp Up

instance Functorial f d c => Profunctor (Up c f) c d (->) where
  dimap f g h = Up $ map g . runUp h . f

newtype Down (d :: y -> y -> *) (f :: x -> y) (a :: x) (b :: y) = Down { runDown :: d (f a) b }

_Down :: Iso (->) (Down d f a b) (Down d' f' a' b') (d (f a) b) (d' (f' a') b')
_Down = dimap runDown Down

instance Functorial f c d => Profunctor (Down d f) c d (->) where
  dimap f g h = Down $ g . runDown h . map f

class (Category c, Category d, Category e) => Bifunctor
    (p :: x -> y -> z)
    (c :: x -> x -> *)
    (d :: y -> y -> *)
    (e :: z -> z -> *)
    | p -> c d e where

  bimap  :: c a a' -> d b b' -> e (p a b) (p a' b')

  first  :: c a a' -> e (p a b) (p a' b)
  first f = bimap f id

  second :: d b b' -> e (p a b) (p a b')
  second = bimap id

instance Bifunctor (,) (->) (->) (->) where
  bimap  = (Arrow.***)
  first  = Arrow.first
  second = Arrow.second

instance Bifunctor Either (->) (->) (->) where
  bimap = (Arrow.+++)
  first = Arrow.left
  second = Arrow.right

instance Bifunctor p (->) (->) (->) => Bifunctor (Natural p) Nat Nat Nat where
  bimap (Nat f) (Nat g) = Nat $ _Natural $ bimap f g
  first (Nat f) = Nat $ _Natural $ first f
  second (Nat f) = Nat $ _Natural $ second f

class Bifunctor p k k k => Tensor (p :: x -> x -> x) (k :: x -> x -> *) | p -> k where
  type Id p :: x
  associate :: Iso k (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))
  lambda    :: Iso k (p (Id p) a) (p (Id p) a') a a'
  rho       :: Iso k (p a (Id p)) (p a' (Id p)) a a'

instance Tensor (,) (->) where
  type Id (,) = ()
  associate = dimap (\((a,b),c) -> (a,(b,c))) (\(a,(b,c)) -> ((a,b),c))
  lambda    = dimap (\((),a) -> a) ((,)())
  rho       = dimap (\(a,()) -> a) (\a -> (a,()))

instance Tensor Either (->) where
  type Id Either = Void
  associate = dimap hither yon where
    hither (Left (Left a)) = Left a
    hither (Left (Right b)) = Right (Left b)
    hither (Right c) = Right (Right c)
    yon (Left a) = Left (Left a)
    yon (Right (Left b)) = Left (Right b)
    yon (Right (Right c)) = Right c
  lambda = dimap (\(Right a) -> a) Right
  rho = dimap (\(Left a) -> a) Left

instance Tensor p (->) => Tensor (Natural p) Nat where
  type Id (Natural p) = K (Id p)
  associate = dimap (Nat $ _Natural $ second (review _Natural) . view associate . first (view _Natural))
                    (Nat $ _Natural $ first (review _Natural) . review associate . second (view _Natural))
  lambda = dimap (Nat $ view lambda . first runK . (view _Natural))
                 (Nat $ review _Natural . first K . review lambda)
  rho = dimap (Nat $ view rho . second runK . view _Natural)
              (Nat $ review _Natural . second K . review rho)

class Tensor p k => Braided (p :: x -> x -> x) (k :: x -> x -> *) | p -> k where
  braid :: Iso k (p a b) (p a' b') (p b a) (p b' a')
  default braid :: Symmetric p k => Iso k (p a b) (p a' b') (p b a) (p b' a')
  braid = dimap swap swap

-- this should be Braided as well, but we can't nicely model that with p -> k!
class Category k => Balanced (k :: x -> x -> *) where
  -- @twist = braid . (twist &&& twist) . braid@
  twist :: k a a

class Braided p k => Symmetric (p :: x -> x -> x) (k :: x -> x -> *) | p -> k where
  swap :: k (p a b) (p b a)
  default swap :: (Cartesian k, p ~ Product k) => k (p a b) (p b a)
  swap = snd &&& fst

{-
class Tensor p k => Auto k | p -> k where
  type Rigid :: x -> x
  unitRigid :: k (Id p) (p (Rigid a) a)
  counitRigid :: k (p a (Rigid a)) (Id p)
-}

instance Braided (,) (->)
instance Symmetric (,) (->) where
  swap (x,y) = (y,x)

instance Braided Either (->)
instance Symmetric Either (->) where
  swap = either Right Left

instance Braided p (->) => Braided (Natural p) Nat where
  braid = dimap (Nat $ _Natural $ review braid) (Nat $ _Natural $ view braid)
instance Symmetric p (->) => Symmetric (Natural p) Nat where
  swap = Nat $ _Natural swap

class Category k => HasTerminal (k :: i -> i -> *) where
  type Terminal k :: i
  terminal :: k x (Terminal k)

instance HasTerminal (->) where
  type Terminal (->) = ()
  terminal _ = ()

instance HasTerminal Nat where
  type Terminal Nat = K ()
  terminal = Nat $ \_ -> K ()

class (Symmetric (Product e) e, HasTerminal e, Terminal e ~ Id (Product e)) => Cartesian (e :: z -> z -> *) where
  type Product e :: z -> z -> z
  fst   :: e (Product e a b) a
  snd   :: e (Product e a b) b
  (&&&) :: e a b -> e a c -> e a (Product e b c)

instance Cartesian (->) where
  type Product (->) = (,)
  fst   = Prelude.fst
  snd   = Prelude.snd
  (&&&) = (Arrow.&&&)

instance Cartesian Nat where
  type Product Nat = Natural (,)
  fst = Nat $ fst . (view _Natural)
  snd = Nat $ snd . (view _Natural)
  Nat f &&& Nat g = Nat $ review _Natural . (f &&& g)

class (Profunctor p k k (->), Cartesian k) => Strong p k | p -> k where
  {-# MINIMAL _1 | _2 #-}
  _1  :: p a b -> p (Product k a x) (Product k b x)
  _1 = dimap swap swap . _2
  _2 :: p a b -> p (Product k x a) (Product k x b)
  _2 = dimap swap swap . _1

instance Strong (->) (->) where
  _1 = first
  _2 = second

instance Strong Nat Nat where
  _1 = first
  _2 = second

type Lens k s t a b = forall p. Strong p k => p a b -> p s t

class Category k => HasInitial (k :: i -> i -> *) where
  type Initial k :: i
  initial :: k (Initial k) x

instance HasInitial (->) where
  type Initial (->) = Void
  initial = absurd

instance HasInitial Nat where
  type Initial Nat = K Void
  initial = Nat $ absurd . runK

class (Symmetric (Sum k) k, HasInitial k, Initial k ~ Id (Sum k)) => Cocartesian (k :: i -> i -> *) where
  type Sum k :: i -> i -> i
  inl    :: k x (Sum k x y)
  inr    :: k y (Sum k x y)
  (|||)  :: k x z -> k y z -> k (Sum k x y) z

instance Cocartesian (->) where
  type Sum (->) = Either
  inl = Left
  inr = Right
  (|||) = either

instance Cocartesian Nat where
  type Sum Nat = Natural Either
  inl = Nat (review _Natural . Left)
  inr = Nat (review _Natural . Right)
  Nat f ||| Nat g = Nat $ either f g . view _Natural

class (Profunctor p k k (->), Cocartesian k) => Choice p k | p -> k where
  {-# MINIMAL _Left | _Right #-}
  _Left  :: p a b -> p (Sum k a x) (Sum k b x)
  _Left = dimap swap swap . _Right
  _Right :: p a b -> p (Sum k x a) (Sum k x b)
  _Right = dimap swap swap . _Left

instance Choice (->) (->) where
  _Left = Arrow.left
  _Right = Arrow.right

instance Choice Nat Nat where
  _Left (Nat f) = Nat $ _Natural (_Left f)
  _Right (Nat g) = Nat $ _Natural (_Right g)

type Prism k s t a b = forall p. Choice p k => p a b -> p s t

type AdjunctionIso f u c d = forall a b a' b'. Iso (->) (c (f a) b) (c (f a') b') (d a (u b)) (d a' (u b'))

class (Functorial f d c, Functorial u c d) => Adjunction (f :: y -> x) (u :: x -> y) (c :: x -> x -> *) (d :: y -> y -> *) | f -> u c d, u -> f c d where
  adjunction :: AdjunctionIso f u c d

unitAdj :: Adjunction f u c d => d a (u (f a))
unitAdj = view adjunction id

counitAdj :: Adjunction f u c d => c (f (u b)) b
counitAdj = review adjunction id

class (Profunctor (Exp k) k k k, Cartesian k) => CCC (k :: x -> x -> *) where
  type Exp k :: x -> x -> x
  curried :: Iso (->) (Product k a b `k` c) (Product k a' b' `k` c') (a `k` Exp k b c) (a' `k` Exp k b' c')

apply :: CCC k => Product k (Exp k b c) b `k` c
apply = review curried id

unapply :: CCC k => a `k` Exp k b (Product k a b)
unapply = view curried id

cccAdjunction :: CCC k => AdjunctionIso (Product k e) (Exp k e) k k
cccAdjunction = dimap (. swap) (. swap) . curried

instance CCC (->) where
  type Exp (->) = (->)
  curried = dimap curry uncurry

instance Adjunction ((,) e) ((->) e) (->) (->) where
  adjunction = cccAdjunction

instance CCC Nat where
  type Exp Nat = Natural (->)
  curried = dimap hither yon where
    hither (Nat f) = Nat $ \a -> (review _Natural) $ \b -> f ((review _Natural) (a, b))
    yon (Nat f) = Nat $ \(Natural (a,b)) -> (view _Natural) (f a) b

instance Adjunction (Natural (,) e) (Natural (->) e) Nat Nat where
  adjunction = cccAdjunction

class (Functorial (Rep p) d c, Profunctor p c d (->)) => Representable (p :: x -> y -> *) (c :: x -> x -> *) (d :: y -> y -> *) | p -> c d where
  type Rep p :: y -> x
  rep :: Iso (->) (p a b) (p a' b') (c a (Rep p b)) (c a' (Rep p b'))

instance Representable (->) (->) (->) where
  type Rep (->) = Identity
  rep = dimap (Identity.) (runIdentity.)

instance Functorial f d c => Representable (Up c f) c d where
  type Rep (Up c f) = f
  rep = _Up

class (Functorial (Corep p) c d, Profunctor p c d (->)) => Corepresentable (p :: x -> y -> *) (c :: x -> x -> *) (d :: y -> y -> *) | p -> c d where
  type Corep p :: x -> y
  corep :: Iso (->) (p a b) (p a' b') (d (Corep p a) b) (d (Corep p a') b')

instance Corepresentable (->) (->) (->) where
  type Corep (->) = Identity
  corep = dimap (.runIdentity) (.Identity)

instance Functorial f c d => Corepresentable (Down d f) c d where
  type Corep (Down d f) = f
  corep = _Down

-- A strong monoidal functor in a CCC, aka Applicative
class (Functorial f c c, CCC c) => MonoidalCCC (f :: x -> x) (c :: x -> x -> *) | f -> c where
  pure  :: a `c` f a
  (<*>) :: f (Exp c a b) `c` Exp c (f a) (f b)

type Traversal k s t a b = forall p. (Strong p k, Representable p k k, MonoidalCCC (Rep p) k) => p a b -> p s t

both :: Traversal (->) (a, a) (b, b) a b
both pab = review rep $ \(a1, a2) -> let f = view rep pab in (,) <$> f a1 <*> f a2

newtype WrapMonoidal f a = WrapMonoidal { unwrapMonoidal :: f a }

instance MonoidalCCC f (->) => Functor (WrapMonoidal f) where
  fmap f = WrapMonoidal . map f . unwrapMonoidal

instance MonoidalCCC f (->) => Applicative.Applicative (WrapMonoidal f) where
  pure a = WrapMonoidal $ pure a
  WrapMonoidal ff <*> WrapMonoidal fa = WrapMonoidal $ ff <*> fa

traversing :: Traversable t => Traversal (->) (t a) (t b) a b
traversing = review rep . (unwrapMonoidal .) . traverse . (WrapMonoidal .) . view rep

newtype Evil i p a b = Evil { runEvil :: p (a i) (b i) }
_Evil = dimap runEvil Evil

newtype Unnatural (j :: x) (p :: y -> y -> *) (a :: x -> y) (b :: x -> y) (i :: x) = Unnatural { runUnnatural :: p (a i) (b i) }
_Unnatural = dimap runUnnatural Unnatural

instance Category k => Category (Evil i k) where
  id = Evil id
  Evil f . Evil g = Evil (f . g)

instance Profunctor p c d (->) => Profunctor (Evil i p) (Evil i c) (Evil i d) (->) where
  dimap (Evil f) (Evil g) = _Evil (dimap f g)

instance Bifunctor p c d (->) => Bifunctor (Evil i p) (Evil i c) (Evil i d) (->) where
  bimap (Evil f) (Evil g) = _Evil (bimap f g)

instance Profunctor p c d (->) => Profunctor (Unnatural i p) (Evil i c) (Evil i d) (Evil i (->)) where
  dimap (Evil f) (Evil g) = Evil $ _Unnatural (dimap f g)

instance Bifunctor p c d (->) => Bifunctor (Unnatural i p) (Evil i c) (Evil i d) (Evil i (->)) where
  bimap (Evil f) (Evil g) = Evil $ _Unnatural (bimap f g)

instance Tensor p (->) => Tensor (Unnatural i p) (Evil i (->)) where
  type Id (Unnatural i p) = K (Id p)
  associate = dimap (Evil $ _Unnatural $ second (review _Unnatural) . view associate . first (view _Unnatural))
                    (Evil $ _Unnatural $ first (review _Unnatural) . review associate . second (view _Unnatural))
  lambda = dimap (Evil $ view lambda . first runK . (view _Unnatural))
                 (Evil $ review _Unnatural . first K . review lambda)
  rho = dimap (Evil $ view rho . second runK . view _Unnatural)
              (Evil $ review _Unnatural . second K . review rho)

apIx :: MonoidalCCC f Nat => f (Natural (->) a b) i -> f a i -> f b i
apIx = view _Natural . runNat (<*>)

pureIx :: MonoidalCCC f Nat => a i -> f a i
pureIx = runNat pure

mapIx :: MonoidalCCC f Nat => (a i -> b i) -> f a i -> f b i
mapIx f fa = pureIx (review _Natural f) `apIx` fa

liftA2Ix :: MonoidalCCC f Nat => (a i -> b i -> c i) -> f a i -> f b i -> f c i
liftA2Ix f fa fb = pureIx (review _Natural $ review _Natural . f) `apIx` fa `apIx` fb

liftA3Ix :: MonoidalCCC f Nat => (a i -> b i -> c i -> d i) -> f a i -> f b i -> f c i -> f d i
liftA3Ix f fa fb fc = pureIx (review _Natural $ (review _Natural .) $ (review _Natural .) . f) `apIx` fa `apIx` fb `apIx` fc

data (||) :: * -> * -> Bool -> * where
  Fst :: a -> (a || b) False
  Snd :: b -> (a || b) True

{-
data Poly p i a b where
  Poly :: p (a i) (b i)

poly :: Profunctor p (->) (->) (->) => (forall i. Poly p i (K a) (K b) -> Poly p i (K s) (K t)) -> p a b -> p s t
poly l = undefined
-}

this :: Traversal Nat (a || b) (c || b) (K a) (K c)
this pac = review rep $ Nat $ \s -> case s of
  Fst a -> (\(K c) -> Fst c) `mapIx` runNat (view rep pac) (K a)
  Snd b -> pureIx (Snd b)

that :: Traversal Nat (a || b) (a || c) (K b) (K c)
that pbc = review rep $ Nat $ \s -> case s of
  Fst a -> pureIx (Fst a)
  Snd b -> (\(K c) -> Snd c) `mapIx` runNat (view rep pbc) (K b)

-- The following is for completeness

class (Functorial f c d, Tensor p c, Tensor q d) => Monoidal f p q c d | f -> p q c d where
  unit :: Id q `d` f (Id p)
  mult :: q (f a) (f b) `d` f (p a b)

class (Monoidal f p q c d, Tensor p c, Tensor q d) => Strength f p q c d | f -> p q c d where
  strength :: q a (f b) `d` f (p a b)

-- messy
instance (CCC c, Monoidal f (Product c) (Product c) c c, Strength f (Product c) (Product c) c c) => MonoidalCCC f c where
  pure = map (view rho) . strength . second unit . review rho
  (<*>) = view curried (map apply . mult)
