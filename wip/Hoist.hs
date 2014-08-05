{-# LANGUAGE ScopedTypeVariables, RankNTypes, KindSignatures, TypeOperators, TupleSections #-}
module Hoist where

import Control.Applicative
import Control.Category
import Control.Monad (liftM, ap)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Identity
import Data.Constraint hiding (trans)
import Prelude hiding ((.),id)

-- | Monad transformer homomorphisms
newtype Hom s t = Hom { runHom :: forall m a. Monad m => s m a -> t m a }

instance Category Hom where
  id = Hom id
  Hom f . Hom g = Hom (f . g)

-- | Monad transformers with proof
class Trans (t :: (* -> *) -> * -> *) where
  lift  :: Monad m => m a -> t m a 
  trans :: Monad m => Dict (Monad (t m))

instance Trans IdentityT where
  lift = IdentityT
  trans = Dict

instance Trans (StateT s) where
  lift m = StateT $ \s -> liftM (,s) m
  trans = Dict

instance Trans (ReaderT s) where
  lift m = ReaderT $ const m
  trans = Dict

class Trans t => Hoist t where
  hoist :: (Monad m, Monad n) => (forall a. m a -> n a) -> t m b -> t n b

instance Hoist IdentityT where
  hoist mn (IdentityT m) = IdentityT (mn m)

instance Hoist (StateT s) where
  hoist mn (StateT m) = StateT $ \s -> mn (m s)

-- | Profunctor into a monad transformer stack
class Profunctor (p :: ((* -> *) -> * -> *) -> ((* -> *) -> * -> *) -> *) where
  lmap  :: (Hoist s, Hoist a, Trans b) => Hom s a -> p a b -> p s b
  dimap :: (Hoist s, Hoist t, Hoist a, Hoist b) => Hom s a -> Hom b t -> p a b -> p s t

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

class Profunctor p => Strong p where
  _1 :: (Hoist a, Hoist b, Trans c) => p a b -> p (Tensor a c) (Tensor b c)
  _2 :: (Trans a, Trans b, Hoist c) => p a b -> p (Tensor c a) (Tensor c b)

type Lens s t a b = forall p. Strong p => p a b -> p s t

-- | Monoidal tensor for the category of monad transformers
--
-- This performs the nesting.
newtype Tensor (s :: (* -> *) -> * -> *) (t :: (* -> *) -> * -> *) (m :: * -> *) (a :: *) = Tensor { runTensor :: s (t m) a }

instance (Trans s, Trans t) => Trans (Tensor s t) where
  lift = go where
    go :: forall m a. Monad m => m a -> Tensor s t m a
    go m = case trans :: Dict (Monad (t m)) of
      Dict -> Tensor $ lift $ lift m
  trans = Dict

instance (Hoist s, Hoist t) => Hoist (Tensor s t) where
  hoist = go where
    go :: forall m n b. (Monad m, Monad n) => (forall a. m a -> n a) -> Tensor s t m b -> Tensor s t n b
    go mn (Tensor stm) = Tensor $ case trans :: Dict (Monad (t m)) of
      Dict -> case trans :: Dict (Monad (t n)) of
        Dict -> hoist (hoist mn) stm

instance (Trans s, Trans t, Monad m) => Functor (Tensor s t m) where
  fmap = liftM

instance (Trans s, Trans t, Monad m) => Applicative (Tensor s t m) where
  pure = return
  (<*>) = ap

instance (Trans s, Trans t, Monad m) => Monad (Tensor s t m) where
  return a = lift (return a)
  (>>=) = go where
    go :: forall a b. Tensor s t m a -> (a -> Tensor s t m b) -> Tensor s t m b
    go (Tensor m) f = Tensor $ case trans :: Dict (Monad (t m)) of
      Dict -> case trans :: Dict (Monad (s (t m))) of
        Dict -> m >>= runTensor . f

lambda :: (Hoist s, Hoist t) => Iso (Tensor IdentityT s) (Tensor IdentityT t) s t
lambda = dimap (Hom (runIdentityT . runTensor)) (Hom (Tensor . IdentityT))

rho :: (Hoist s, Hoist t) => Iso (Tensor s IdentityT) (Tensor t IdentityT) s t
rho = dimap (Hom (hoist runIdentityT . runTensor)) (Hom (Tensor . hoist IdentityT))

associate :: forall s t u s' t' u'. (Hoist s, Hoist t, Hoist u, Hoist s', Hoist t', Hoist u')
          => Iso (Tensor (Tensor s t) u) (Tensor (Tensor s' t') u')
                 (Tensor s (Tensor t u)) (Tensor s' (Tensor t' u'))
associate = dimap (Hom hither) (Hom yon) where
  hither :: forall m a. Monad m => Tensor (Tensor s t) u m a -> Tensor s (Tensor t u) m a
  hither (Tensor (Tensor m)) = case trans :: Dict (Monad (u m)) of
    Dict -> case trans :: Dict (Monad (t (u m))) of
      Dict -> Tensor (hoist Tensor m)
  yon :: forall m a. Monad m => Tensor s' (Tensor t' u') m a -> Tensor (Tensor s' t') u' m a
  yon (Tensor m) = case trans :: Dict (Monad (u' m)) of
    Dict -> case trans :: Dict (Monad (t' (u' m))) of
     Dict -> Tensor (Tensor (hoist runTensor m))

-- given a normal lens we can a lens into state
ahoy :: (Hoist t, Hoist s, Hoist s') => Lens (Tensor t s) (Tensor t s') s s'
ahoy = _2
