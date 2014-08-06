{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- @
-- Prof  :: (j -> k -> *) -> (i -> j -> *) -> i -> k -> *
-- ProfR :: (i -> j -> *) -> (i -> k -> *) -> j -> k -> *
-- @
--------------------------------------------------------------------
module Hask.Prof where

import Hask.Core

-- forward profunctor composition forms a weak category.
data Prof :: (j -> k -> *) -> (i -> j -> *) -> i -> k -> * where
  Prof :: p b c -> q a b -> Prof p q a c

instance Category ((~>) :: i -> i -> *) => Semitensor (Prof :: (i -> i -> *) -> (i -> i -> *) -> i -> i -> *) where
  type Tensorable Prof = Profunctor
  second = fmap1
  associate = associateProf

type instance I Prof = (~>)
instance Category ((~>) :: i -> i -> *) => Tensor (Prof :: (i -> i -> *) -> (i -> i -> *) -> i -> i -> *) where
  lambda = lambdaProf
  rho = rhoProf

instance Functor Prof where
  fmap f = nat3 $ \(Prof p q) -> Prof (transport2 f p) q

instance Functor (Prof p) where
  fmap f = nat2 $ \(Prof p q) -> Prof p (transport2 f q)

instance Contravariant q => Contravariant (Prof p q) where
  contramap f = Nat $ \(Prof p q) -> Prof p (transport (contramap f) q)

instance Post Functor p => Functor (Prof p q a) where
  fmap f (Prof p q) = Prof (fmap1 f p) q

instance Functor q => Functor (Prof p q) where
  fmap f = Nat $ \(Prof p q) -> Prof p (transport (fmap f) q)

instance Post Contravariant p => Contravariant (Prof p q a) where
  contramap f (Prof p q) = Prof (contramap1 f p) q

associateProf :: Iso (Prof (Prof p q) r) (Prof (Prof p' q') r')
                     (Prof p (Prof q r)) (Prof p' (Prof q' r'))
associateProf = dimap
  (nat2 $ \ (Prof (Prof a b) c) -> Prof a (Prof b c))
  (nat2 $ \ (Prof a (Prof b c)) -> Prof (Prof a b) c)

whiskerProfL :: (p ~> q) -> Prof p r ~> Prof q r
whiskerProfL = first

whiskerProfR :: (p ~> q) -> Prof l p ~> Prof l q
whiskerProfR = fmap

lambdaProf :: (Category k, k ~ Hom, Post Functor p) => Iso (Prof k p) (Prof k q) p q
lambdaProf = dimap (nat2 $ \(Prof k p) -> fmap1 k p) (nat2 $ Prof id)

rhoProf :: (Category k, k ~ Hom, Contravariant p) => Iso (Prof p k) (Prof q k) p q
rhoProf = dimap (nat2 $ \(Prof p k) -> lmap k p) (nat2 $ \q -> Prof q id)

newtype ProfR p q a b = ProfR { runProfR :: forall x. p x a -> q x b }

instance Contravariant ProfR where
  contramap f = nat3 $ \(ProfR pq) -> ProfR $ \p -> pq (transport2 f p)

instance Functor (ProfR p) where
  fmap f = nat2 $ \(ProfR pq) -> ProfR $ \p -> transport2 f (pq p)

instance Post Functor p => Contravariant (ProfR p q) where
  contramap f = Nat $ \(ProfR pq) -> ProfR $ \p -> pq (fmap1 f p)

instance Post Functor q => Functor (ProfR p q a) where
  fmap f (ProfR pq) = ProfR $ \p -> fmap1 f (pq p)

instance Post Contravariant p => Functor (ProfR p q) where
  fmap f = Nat $ \(ProfR pq) -> ProfR $ \p -> pq (contramap1 f p)

instance Post Contravariant q => Contravariant (ProfR p q a) where
  contramap f (ProfR pq) = ProfR $ \p -> contramap1 f (pq p)

type instance I ProfR = (~>)

iotaProf :: (Category p, p ~ (~>), Contravariant q') => Iso (ProfR p q) (ProfR (~>) q') q q'
iotaProf = dimap (nat2 $ \(ProfR f) -> f id) (nat2 $ \f -> ProfR $ \p -> lmap p f)

jotProf :: Post Functor p => (~>) ~> ProfR p p
jotProf = nat2 $ \f -> ProfR (fmap1 f)

instance Curried Prof ProfR where
  curry k = nat2 $ \p -> ProfR $ \q -> transport2 k (Prof p q)
  uncurry k = nat2 $ \(Prof p q) -> runProfR (transport2 k p) q

-- To cocurry Prof we'd have the following universal property:

--newtype ProfL p q a b = ProfL { runProfL :: forall r. (q ~> Prof r p) ~> r a b }
--
--instance Cocurried ProfL Prof where
--  uncocurry l = nat2 $ \k -> runProfL k l
--
--  -- but to cocurry, we'd need to be able to 'smuggle information out' in c.
--  cocurry l = nat2 $ \b -> case transport2 l (ProfL $ \f -> case transport2 f b of Prof p q -> _uh) of
--    x -> _wat

