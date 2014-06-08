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
import Control.Applicative
import Control.Category
import Data.Bitraversable
import Data.Functor.Identity
import Data.Monoid hiding (Product, Sum)
import Data.Traversable
import Data.Type.Equality
import Data.Typeable
import Data.Void
import Prelude hiding (map, id, (.), fst, snd)
import qualified Prelude

-- * Enriched Profunctors
-- p : C^op x D -> E
class (Category c, Category d, Category e) => Profunctor (p :: x -> y -> z) (c :: x -> x -> *) (d :: y -> y -> *) (e :: z -> z -> *) | p -> c d e where
  dimap :: c a a' -> d b b' -> e (p a' b) (p a b')

  lmap :: c a a' -> e (p a' b) (p a b)
  lmap f = dimap f id

  rmap :: d b b' -> e (p a b) (p a b')
  rmap = dimap id

instance Profunctor (->) (->) (->) (->) where
  dimap f g h = g . h . f

type Iso c d s t a b = forall p. Profunctor p c d (->) => p a b -> p s t

newtype Hom k a b = Hom { runHom :: k a b }

instance Category k => Profunctor (Hom k) k k (->) where
  dimap f g h = Hom $ g . runHom h . f

_Hom :: Iso (->) (->) (Hom k a b) (Hom k' a' b') (k a b) (k' a' b')
_Hom = dimap runHom Hom

-- * Viewing

newtype Forget c r a b = Forget { runForget :: c a r }

instance Category k => Profunctor (Forget k r) k k (->) where
  dimap f _ (Forget ar) = Forget (ar . f)

_Forget :: Iso (->) (->) (Forget c r a b) (Forget c' r' a' b') (c a r) (c' a' r')
_Forget = dimap runForget Forget

view :: Category k => (Forget k a a a -> Forget k a s s) -> k s a
view l = runForget $ l (Forget id)

newtype From p a b s t = From { runFrom :: p t s -> p b a }

_From :: Iso (->) (->) (From p a b s t) (From p' a' b' s' t') (p t s -> p b a) (p' t' s' -> p' b' a')
_From = dimap runFrom From

instance Profunctor p d c (->) => Profunctor (From p a b) c d (->) where
  dimap f g = _From $ lmap (dimap g f)

from :: (From p a b a b -> From p a b s t) -> p t s -> p b a
from l = runFrom $ l (From id)

review :: Category k => (From (Forget k a) s s s s -> From (Forget k a) s s a a) -> k s a
review = view.from

-- * Natural transformations

-- newtype NAT (d :: y -> y -> *) (f :: x -> y) (g :: x -> y) = Nat { runNat :: forall a. d (f a) (g a) }

newtype Nat x y = Nat { runNat :: forall i. x i -> y i }

instance Category Nat where
  id = Nat id
  Nat f . Nat g = Nat (f . g)

instance Profunctor Nat Nat Nat (->) where
  dimap (Nat f) (Nat g) (Nat h) = Nat (dimap f g h)

-- * Lifting bifunctors

newtype Lift p f g a = Lift { lower :: p (f a) (g a) } -- could be used with Lift (,), Lift Either, Lift (->) to get corresponding entries for Nat

_Lift :: Iso (->) (->) (Lift p f g a) (Lift p' f' g' a') (p (f a) (g a)) (p' (f' a') (g' a'))
_Lift = dimap lower Lift

data (*) f g a = Product (f a) (g a) deriving (Eq,Ord,Show,Read,Typeable)
data (+) f g a = L (f a) | R (g a) deriving (Eq,Ord,Show,Read,Typeable)
data Pow f g a = Pow { runPow :: f a -> g a } deriving Typeable

_Pow :: Iso (->) (->) (Pow f g a) (Pow f' g' a') (f a -> g a) (f' a' -> g' a')
_Pow = dimap runPow Pow

instance Functorial ((*) f) Nat Nat where
  map = bimap id

instance Functorial ((+) f) Nat Nat where
  map = bimap id

instance Profunctor Pow Nat Nat Nat where
  dimap (Nat f) (Nat h) = Nat $ \(Pow g) -> Pow (h . g . f)

instance Functorial (Pow f) Nat Nat where
  map = rmap

data One a = One deriving (Eq,Ord,Show,Read,Typeable)
newtype K b a = K b deriving (Eq,Ord,Show,Read,Typeable)
newtype An f a = An (f a) deriving (Eq,Ord,Show,Read,Typeable)

data Zero a deriving Typeable
instance Show (Zero a) where showsPrec _ x = seq x undefined
instance Eq (Zero a) where a == b = seq a $ seq b True
instance Ord (Zero a) where compare a b = seq a $ seq b EQ

data Procompose (p :: x -> y -> *) (q :: y -> z -> *) (d :: x) (c :: z) where
  Procompose :: p d a -> q a c -> Procompose p q d c

instance (Profunctor p c d (->), Profunctor q d e (->)) => Profunctor (Procompose p q) c e (->) where
  dimap f g (Procompose p q) = Procompose (lmap f p) (rmap g q)

newtype Up (c :: x -> x -> *) (f :: y -> x) (a :: x) (b :: y)  = Up { runUp :: c a (f b) }

_Up :: Iso (->) (->) (Up c f a b) (Up c' f' a' b') (c a (f b)) (c' a' (f' b'))
_Up = dimap runUp Up

newtype Down (d :: y -> y -> *) (f :: x -> y) (a :: x) (b :: y) = Down { runDown :: d (f a) b }

_Down :: Iso (->) (->) (Down d f a b) (Down d' f' a' b') (d (f a) b) (d' (f' a') b')
_Down = dimap runDown Down

class (Category c, Category d) => Functorial f c d | f c -> d, f d -> c where
  map :: c a b -> d (f a) (f b)

instance Functor g => Functorial g (->) (->) where
  map = fmap

instance Functorial f d c => Profunctor (Up c f) c d (->) where
  dimap f g (Up h) = Up $ map g . h . f

instance Functorial f c d => Profunctor (Down d f) c d (->) where
  dimap f g (Down h) = Down $ g . h . map f

class (Category c, Category d, Category e) => Bifunctor (p :: x -> y -> z) (c :: x -> x -> *) (d :: y -> y -> *) (e :: z -> z -> *) | p -> c d e where
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

instance Bifunctor (*) Nat Nat Nat where
  bimap (Nat f) (Nat g) = Nat $ \(Product as bs) -> Product (f as) (g bs)
  first (Nat f)  = Nat $ \(Product as bs) -> Product (f as) bs
  second (Nat g) = Nat $ \(Product as bs) -> Product as (g bs)

instance Bifunctor (+) Nat Nat Nat where
  bimap (Nat f) (Nat g) = Nat $ \ xs -> case xs of
    L a -> L (f a)
    R b -> R (g b)

class Bifunctor p k k k => Tensor (p :: x -> x -> x) (k :: x -> x -> *) | p -> k where
  type Id p :: x
  associate :: Iso k k (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))
  lambda    :: Iso k k (p (Id p) a) (p (Id p) a') a a'
  rho       :: Iso k k (p a (Id p)) (p a' (Id p)) a a'

instance Tensor (,) (->) where
  type Id (,) = ()
  associate = dimap (\((a,b),c) -> (a,(b,c))) (\(a,(b,c)) -> ((a,b),c))
  lambda    = dimap (\((),a) -> a) ((,)())
  rho       = dimap (\(a,()) -> a) (\a -> (a,()))

instance Tensor (*) Nat where
  type Id (*) = One
  associate = dimap hither yon where
    hither = Nat $ \(Product (Product as bs) cs) -> Product as (Product bs cs)
    yon = Nat $ \(Product as (Product bs cs)) -> Product (Product as bs) cs
  lambda = dimap hither yon where
    hither = Nat $ \(Product One as) -> as
    yon = Nat $ \as -> Product One as
  rho = dimap hither yon where
    hither = Nat $ \(Product as One) -> as
    yon = Nat (\as -> Product as One)

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

instance Tensor (+) Nat where
  type Id (+) = Zero
  associate = dimap hither yon where
    hither = Nat $ \xs -> case xs of
      L (L a) -> L a
      L (R b) -> R (L b)
      R c     -> R (R c)
    yon = Nat $ \xs -> case xs of
      L a     -> L (L a)
      R (L b) -> L (R b)
      R (R c) -> R c
  lambda = dimap (Nat $ \(R a) -> a) (Nat R)
  rho    = dimap (Nat $ \(L a) -> a) (Nat L)

class (Functorial f k k, Tensor p k) => Monoidal f p k | f -> p k where
  unit :: Id p `k` f (Id p)
  mult :: p (f a) (f b) `k` f (p a b)

instance Applicative f => Monoidal f (,) (->) where
  unit = pure
  mult = uncurry (liftA2 (,))

class Tensor p k => Symmetric (p :: x -> x -> x) (k :: x -> x -> *) | p -> k where
  swap :: k (p a b) (p b a)
  default swap :: (Cartesian k, p ~ Product k) => k (p a b) (p b a)
  swap = snd &&& fst

instance Symmetric (,) (->) where
  swap (x,y) = (y,x)

instance Symmetric Either (->) where
  swap = either Right Left

instance Symmetric (*) Nat where
  swap = Nat $ \ (Product as bs) -> Product bs as

instance Symmetric (+) Nat where
  swap = Nat $ \ xs -> case xs of
    L a -> R a
    R a -> L a

class (Category k) => HasTerminal (k :: i -> i -> *) where
  type Terminal k :: i
  terminal :: k x (Terminal k)

instance HasTerminal (->) where
  type Terminal (->) = ()
  terminal = const ()

instance HasTerminal Nat where
  type Terminal Nat = One
  terminal = Nat (const One)

class (Symmetric (Product k) k, HasTerminal k, Terminal k ~ Id (Product k)) => Cartesian (k :: i -> i -> *) where
  type Product k :: i -> i -> i
  fst   :: k (Product k x y) x
  snd   :: k (Product k x y) y
  (&&&) :: k x y -> k x z -> k x (Product k y z)

instance Cartesian (->) where
  type Product (->) = (,)
  fst   = Prelude.fst
  snd   = Prelude.snd
  (&&&) = (Arrow.&&&)

instance Cartesian Nat where
  type Product Nat = (*)
  fst = Nat $ \(Product as _) -> as
  snd = Nat $ \(Product _ bs) -> bs
  Nat f &&& Nat g = Nat $ \as -> Product (f as) (g as)

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
  type Initial Nat = Zero
  initial = Nat $ \ xs -> xs `seq` undefined

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
  type Sum Nat = (+)
  inl = Nat L
  inr = Nat R
  Nat f ||| Nat g = Nat $ \xs -> case xs of
    L a -> f a
    R b -> g b

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
  _Left (Nat f) = Nat $ \xs -> case xs of
    L a -> L (f a)
    R b -> R b
  _Right (Nat g) = Nat $ \xs -> case xs of
    L a -> L a
    R b -> R (g b)

type Prism k s t a b = forall p. Choice p k => p a b -> p s t

type AdjunctionIso f u c d = forall a b a' b'. Iso (->) (->) (c (f a) b) (c (f a') b') (d a (u b)) (d a' (u b'))

class (Functorial f d c, Functorial u c d) => Adjunction (f :: y -> x) (u :: x -> y) (c :: x -> x -> *) (d :: y -> y -> *) | f -> u c d, u -> f c d where
  adjunction :: AdjunctionIso f u c d

-- unit :: Adjunction f u c d => d a (u (f a))
-- unit = view adjunction id
--
-- counit :: Adjunction f u c d => c (f (u b)) b
-- counit = review adjunction id

class (Profunctor (Exp k) k k k, Cartesian k) => CCC (k :: x -> x -> *) where
  type Exp k :: x -> x -> x
  curried :: Iso (->) (->) (Product k a b `k` c) (Product k a' b' `k` c') (a `k` Exp k b c) (a' `k` Exp k b' c')

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
  type Exp Nat = Pow
  curried = dimap hither yon where
    hither (Nat f) = Nat $ \a -> Pow $ \b -> f (Product a b)
    yon (Nat f) = Nat $ \(Product a b) -> case f a of Pow g -> g b

instance Adjunction ((*) e) (Pow e) Nat Nat where
  adjunction = cccAdjunction

class (Functorial (Rep p) d c, Profunctor p c d (->)) => Representable (p :: x -> y -> *) (c :: x -> x -> *) (d :: y -> y -> *) | p -> c d where
  type Rep p :: y -> x
  rep :: Iso (->) (->) (p a b) (p a' b') (c a (Rep p b)) (c a' (Rep p b'))

instance Representable (->) (->) (->) where
  type Rep (->) = Identity
  rep = dimap (Identity.) (runIdentity.)

instance Functorial f d c => Representable (Up c f) c d where
  type Rep (Up c f) = f
  rep = _Up

type Traversal k s t a b = forall p. (Strong p k, Representable p k k, Monoidal (Rep p) (Product k) k) => p a b -> p s t

both :: Traversal (->) (a, a) (b, b) a b
both pab = review rep $ \(a1, a2) -> let f = view rep pab in mult (f a1, f a2)

traversing :: Traversal (->) [a] [b] a b
traversing pab = review rep f where
  f [] = const [] `map` unit ()
  f (a:as) = uncurry (:) `map` mult (view rep pab a, f as)

{-
type Cotraversal k s t a b = forall p. (Choice p k, Representable p k k, Monoidal (Rep p) (Sum k) k) => p a b -> p s t -- maybe?
-}

class (Functorial (Corep p) c d, Profunctor p c d (->)) => Corepresentable (p :: x -> y -> *) (c :: x -> x -> *) (d :: y -> y -> *) | p -> c d where
  type Corep p :: x -> y
  corep :: Iso (->) (->) (p a b) (p a' b') (d (Corep p a) b) (d (Corep p a') b')

instance Corepresentable (->) (->) (->) where
  type Corep (->) = Identity
  corep = dimap (.runIdentity) (.Identity)

instance Functorial f c d => Corepresentable (Down d f) c d where
  type Corep (Down d f) = f
  corep = _Down

-- Well reasoned code ends. Below here are old ramblings from how I got here.

data (||) :: * -> * -> Bool -> * where
  Fst :: a -> (a || b) False
  Snd :: b -> (a || b) True

{-
{-
class Profunctor p k k => Walkable p k | p -> k where
  pureP :: p a a
  apP :: p a b -> p a c -> p a (Product k b c)

instance Walkable (->) (->) where
  pureP = id
  apP = (Arrow.&&&)


class Category k => Natural (k :: x -> x -> *) (f :: x -> y -> *) | k -> f where
  natural :: k a b -> Nat (f a) (f b)

instance Natural (->) (K :: * -> () -> *) where
  natural f = Nat $ \(K a) -> K (f a)

instance Natural Nat An where
  natural (Nat f) = Nat $ \(An a) -> An (f a)
-}

{-
-- class Functorial (Mu k) (Nat k) k => Fixed k where -- requires a category of natual transformations over our base category. harder to express in haskell
class Fixed (k :: x -> x -> *) where
  type Mu k :: (x -> x) -> x
  type Nu k :: (x -> x) -> x
  cata :: Functorial f k k => k (f a) a -> k (Mu k f) a
  -- cata f = f . map (cata f) . view mu
  ana  :: Functorial f k k => k a (f a) -> k a (Nu k f)
  -- ana g = view nu . map (ana g) . g
  mu   :: Iso k k (f (Mu k f)) (g (Mu k g)) (Mu k f) (Mu k g)
  nu   :: Iso k k (f (Nu k f)) (g (Nu k g)) (Nu k f) (Nu k g)

instance Cartesian k => Strong (Forget k r) k where
  _1 (Forget ar) = Forget (ar . fst)

newtype Fix f = In { out :: f (Fix f) }

instance Fixed (->) where
  type Mu (->) = Fix
  type Nu (->) = Fix
  cata f = f . map (cata f) . out
  ana g  = In . map (ana g) . g
  mu = dimap In out
  nu = dimap In out

newtype FixF f a = InF { outF :: f (FixF f) a }

instance Fixed Nat where
  type Mu Nat = FixF
  type Nu Nat = FixF
  cata f = f . map (cata f) . Nat outF
  ana g = Nat InF . map (ana g) . g
  mu = dimap (Nat InF) (Nat outF)
  nu = dimap (Nat InF) (Nat outF)
-}

-- type Traversal s t a b =

-- bi :: Bitraversable p => Traversal Nat (An (p a c)) (An (p a d)) (a || b) (c || d)
-- bi = undefined


-- type LensLike p k s t a b =

-- poly :: Functor f => ( (Un a) ~> Un b) -> Un s u -> f (Un t u)) -> LensLike f s t a b
-- poly l f s = runUn <$> l (\(Un a) -> Un <$> f a) (Un s)

{-

-- bilenses

type Bilens s t a b c d = forall f. Functor f => (a -> f b) -> (c -> f d) -> s -> f t
type Bitraversal s t a b c d = forall f. Applicative f => (a -> f b) -> (c -> f d) -> s -> f t
type Bifold s a c = forall f. (Applicative f, Contravariant f) => (a -> f a) -> (c -> f c) -> s -> f s
type Bigetter s a c = forall f. (Applicative f, Contravariant f) => (a -> f a) -> (c -> f c) -> s -> f s
type Biprism s t a b c d = forall p f. (Choice p, Applicative f) => p a (f b) -> p c (f d) -> p s (f t)
type Bisetter s t a b c d = forall p f. Settable f => (a -> f b) -> (c -> f d) -> s -> (f t)
type IndexedBitraversal i j s t a b c d = forall p q f. (Indexable i p, Indexable j q, Applicative f) => p a (f b) -> q c (f d) -> s -> f t
type IndexedBifold i j s a c = forall p q f. (Indexable i p, Indexable j q, Applicative f, Contravariant f) => p a (f a) -> q c (f c) -> s -> f s
type IndexedBigetter i j s a c = forall p q f. (Indexable i p, Indexable j q, Applicative f, Contravariant f) => p a (f a) -> q c (f c) -> s -> f s
type IndexedBisetter i j s a c = forall p q f. (Indexable i p, Indexable j q, Settable f) => p a (f a) -> q c (f c) -> s -> f s

type Bioptic p q r f s t a b c d = p a (f b) -> q c (f d) -> r s (f t)

firstOf :: Applicative f => (p a (f b) -> (c -> f c) -> (s -> f t)) -> p a (f b) -> s -> f t
firstOf l f = l f pure
{-# INLINE firstOf #-}

secondOf :: Applicative f => ((a -> f a) -> q c (f d) -> (s -> f t)) -> q c (f d) -> s -> f t
secondOf l = l pure
{-# INLINE secondOf #-}

bimapOf :: (Profunctor p, Profunctor q) => (p a (Identity b) -> q c (Identity d) -> s -> Identity t) -> p a b -> q c d -> s -> t
bimapOf l f g = runIdentity #. l (Identity #. f) (Identity #. g)

bifoldOf :: ((m -> Const m m) -> (m -> Const m m) -> s -> Const m s) -> s -> m
bifoldOf l = getConst #. l Const Const

bifoldMapOf :: (Profunctor p, Profunctor q) => (p a (Const m a) -> q b (Const m b) -> s -> Const m s) -> p a m -> q b m -> s -> m
bifoldMapOf l p q = getConst #. l (Const #. p) (Const #. q)

bifoldrOf :: (Profunctor p, Profunctor q => (p a (Const (Endo r) a) -> q c (Const (Endo r) c) -> s -> Const (Endo r) s) -> p a (r -> r) -> q c (r -> r) -> r -> s -> r
bifoldrOf l p q z = flip appEndo z `rmap` bifoldMapOf l (Endo #. p) (Endo #. q)

-- polylenses

type PolyLens s t a b       = forall p. Strong p => p a b -> p s t
type PolyLens' s a          = forall p. Strong p => p a a -> p s s
type PolyTraversal s t a b  = forall f j. Applicative f => (forall i. a i -> f (b i)) -> s j -> f (t j)
type PolyTraversal' s a     = forall f j. Applicative f => (forall i. a i -> f (a i)) -> s j -> f (s j)
type PolySetter s t a b     = forall f j. Settable f => (forall i. a i -> f (b i)) -> s j -> f (t j)
type PolySetter' s a        = forall f j. Settable f => (forall i. a i -> f (a i)) -> s j -> f (s j)
type PolyGetter s a         = forall f j. (Functor f, Contravariant f) => (forall i. a i -> f (a i)) -> s j -> f (s j)
type PolyFold s a           = forall f j. (Applicative f, Contravariant f) => (forall i. a i -> f (a i)) -> s j -> f (s j)
type PolyLensLike f s t a b = forall j. (forall i. a i -> f (b i)) -> s j -> f (t j)
type PolyLensLike' f s a    = forall j. (forall i. a i -> f (a i)) -> s j -> f (s j)
type PolyPrism s t a b      = forall p f j. (Choice p, Functor f) => (forall i. a i -> f (b i)) -> s j -> f (t j))

bitraversed :: Bitraversable f => PolyTraversal (Un (f a c)) (Un (f b d)) (Bi a c) (Bi b d)
bitraversed = bi bitraverse

runUn :: Un a u -> a
runUn (Un a) = a

mono :: Functor f => LensLike f s t a b -> PolyLensLike f (Un s) (Un t) (Un a) (Un b)
mono l f (Un s) = Un <$> l (fmap runUn . f . Un) s

type Selector f s t a b = forall u. (a -> f b) -> s u -> f (t u)

poly :: Functor f => ((forall i. Un a i -> f (Un b i)) -> Un s '() -> f (Un t '())) -> LensLike f s t a b
poly l f s = runUn <$> l (\(Un a) -> Un <$> f a) (Un s)

bipoly :: Functor f => ((forall i. Bi a c i -> f (Bi b d i)) -> Un s '() -> f (Un t '())) -> Bioptic (->) (->) (->) f s t a b c d
bipoly l f g s = runUn <$> l (\xs -> case xs of L a -> L <$> f a; R b -> R <$> g b) (Un s)

bi :: Functor f => Bioptic (->) (->) (->) f s t a b c d -> PolyLensLike f (Un s) (Un t) (Bi a c) (Bi b d)
bi l f (Un s) = Un <$> l (\a -> f (L a) <&> \(L b) -> b) (\c -> f (R c) <&> \(R d) -> d) s

this :: PolyTraversal (Bi a c) (Bi b c) (Un a) (Un b)
this f (L a) = f (Un a) <&> \ (Un a) -> L a
this f (R b) = pure $ R b

that :: PolyTraversal (Bi c a) (Bi c b) (Un a) (Un b)
that f (L a) = pure $ L a
that f (R b) = f (Un b) <&> \(Un b) -> R b

these :: PolyLens (Bi a a) (Bi b b) (Un a) (Un b)
these f (L a) = f (Un a) <&> \ (Un a) -> L a
these f (R b) = f (Un b) <&> \ (Un b) -> R b

bitraverseOf :: Functor f => PolyLensLike f (Un s) (Un t) (Bi a c) (Bi b d) -> (a -> f b) -> (c -> f d) -> s -> f t
bitraverseOf l p q s = l (\xs -> case xs of
  L a -> L <$> p a
  R b -> R <$> q b) (Un s) <&> \(Un t) -> t

(?) :: PolyLensLike f s t a b -> PolyLensLike f a b c d -> PolyLensLike f s t c d
(?) f g x = f (g x)

class Compos t where
  compos :: PolyTraversal' t t

-}
-}
