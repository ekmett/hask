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

type Iso c s t a b = forall p. Profunctor p c c (->) => p a b -> p s t

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

_Lift :: Iso (->) (Lift p f g a) (Lift p' f' g' a') (p (f a) (g a)) (p' (f' a') (g' a'))
_Lift = dimap lower Lift

data (*) f g a = Product (f a) (g a) deriving (Eq,Ord,Show,Read,Typeable)
data (+) f g a = L (f a) | R (g a) deriving (Eq,Ord,Show,Read,Typeable)
data Pow f g a = Pow { runPow :: f a -> g a } deriving Typeable

_Pow :: Iso (->) (Pow f g a) (Pow f' g' a') (f a -> g a) (f' a' -> g' a')
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

_Up :: Iso (->) (Up c f a b) (Up c' f' a' b') (c a (f b)) (c' a' (f' b'))
_Up = dimap runUp Up

newtype Down (d :: y -> y -> *) (f :: x -> y) (a :: x) (b :: y) = Down { runDown :: d (f a) b }

_Down :: Iso (->) (Down d f a b) (Down d' f' a' b') (d (f a) b) (d' (f' a') b')
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
  associate :: Iso k (p (p a b) c) (p (p a' b') c') (p a (p b c)) (p a' (p b' c'))
  lambda    :: Iso k (p (Id p) a) (p (Id p) a') a a'
  rho       :: Iso k (p a (Id p)) (p a' (Id p)) a a'

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

type AdjunctionIso f u c d = forall a b a' b'. Iso (->) (c (f a) b) (c (f a') b') (d a (u b)) (d a' (u b'))

class (Functorial f d c, Functorial u c d) => Adjunction (f :: y -> x) (u :: x -> y) (c :: x -> x -> *) (d :: y -> y -> *) | f -> u c d, u -> f c d where
  adjunction :: AdjunctionIso f u c d

-- unit :: Adjunction f u c d => d a (u (f a))
-- unit = view adjunction id
--
-- counit :: Adjunction f u c d => c (f (u b)) b
-- counit = review adjunction id

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
  type Exp Nat = Pow
  curried = dimap hither yon where
    hither (Nat f) = Nat $ \a -> Pow $ \b -> f (Product a b)
    yon (Nat f) = Nat $ \(Product a b) -> case f a of Pow g -> g b

instance Adjunction ((*) e) (Pow e) Nat Nat where
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

type Traversal k s t a b = forall p. (Strong p k, Representable p k k, Monoidal (Rep p) (Product k) k) => p a b -> p s t

both :: Traversal (->) (a, a) (b, b) a b
both pab = review rep $ \(a1, a2) -> let f = view rep pab in mult (f a1, f a2)

newtype WrapMonoidal f a = WrapMonoidal { unwrapMonoidal :: f a }

instance Monoidal f (,) (->) => Functor (WrapMonoidal f) where
  fmap f = WrapMonoidal . map f . unwrapMonoidal
instance Monoidal f (,) (->) => Applicative (WrapMonoidal f) where
  pure a = WrapMonoidal $ const a `map` unit ()
  WrapMonoidal ff <*> WrapMonoidal fa = WrapMonoidal $ uncurry ($) `map` mult (ff, fa)

traversing :: Traversable t => Traversal (->) (t a) (t b) a b
traversing = view (from rep) . (unwrapMonoidal .) . traverse . (WrapMonoidal .) . view rep

class (Functorial (Corep p) c d, Profunctor p c d (->)) => Corepresentable (p :: x -> y -> *) (c :: x -> x -> *) (d :: y -> y -> *) | p -> c d where
  type Corep p :: x -> y
  corep :: Iso (->) (p a b) (p a' b') (d (Corep p a) b) (d (Corep p a') b')

instance Corepresentable (->) (->) (->) where
  type Corep (->) = Identity
  corep = dimap (.runIdentity) (.Identity)

instance Functorial f c d => Corepresentable (Down d f) c d where
  type Corep (Down d f) = f
  corep = _Down

data (||) :: * -> * -> Bool -> * where
  Fst :: a -> (a || b) False
  Snd :: b -> (a || b) True
