{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
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

import Control.Category
import Hask.Core
import qualified Prelude
import Prelude (($), undefined)

-- forward profunctor composition forms a weak category.
data Prof :: (j -> k -> *) -> (i -> j -> *) -> i -> k -> * where
  Prof :: p b c -> q a b -> Prof p q a c

instance Category ((~>) :: i -> i -> *) => Semitensor (Prof :: (i -> i -> *) -> (i -> i -> *) -> i -> i -> *) where
  associate = associateProf

instance Functor Prof where
  fmap f = nat3 $ \(Prof p q) -> Prof (runNat2 f p) q

instance Functor (Prof p) where
  fmap f = nat2 $ \(Prof p q) -> Prof p (runNat2 f q)

instance Contravariant q => Contravariant (Prof p q) where
  contramap f = Nat $ \(Prof p q) -> Prof p (runNat (contramap f) q)

instance Post Functor p => Functor (Prof p q a) where
  fmap f (Prof p q) = Prof (fmap1 f p) q

instance Functor q => Functor (Prof p q) where
  fmap f = Nat $ \(Prof p q) -> Prof p (runNat (fmap f) q)

instance Post Contravariant p => Contravariant (Prof p q a) where
  contramap f (Prof p q) = Prof (contramap1 f p) q

associateProf :: Iso (Prof (Prof p q) r) (Prof (Prof p' q') r')
                     (Prof p (Prof q r)) (Prof p' (Prof q' r'))
associateProf = dimap
  (nat2 $ \ (Prof (Prof a b) c) -> Prof a (Prof b c))
  (nat2 $ \ (Prof a (Prof b c)) -> Prof (Prof a b) c)

{-
lambdaProf :: (Contravariant p, Category q, q ~> (~>)) => Prof q p ~> p
lambdaProf = nat2 $ \(Prof h p) -> lmap h p

rhoProf :: (Category q, q ~ (~>)) => p ~> Prof p q
rhoProf = nat2 $ \p -> Prof p id
-}

newtype ProfR p q a b = ProfR { runProfR :: forall x. p x a -> q x b }

instance Contravariant ProfR where
  contramap f = nat3 $ \(ProfR pq) -> ProfR $ \p -> pq (runNat2 f p)

instance Functor (ProfR p) where
  fmap f = nat2 $ \(ProfR pq) -> ProfR $ \p -> runNat2 f (pq p)

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
  curried = dimap (\k -> nat2 $ \p -> ProfR $ \q -> runNat2 k (Prof p q))
                  (\k -> nat2 $ \(Prof p q) -> runProfR (runNat2 k p) q)

-- To cocurry Prof we'd have the following universal property:

--newtype ProfL p q a b = ProfL { runProfL :: forall r. (q ~> Prof r p) ~> r a b }
--
--instance Cocurried ProfL Prof where
--  uncocurry l = nat2 $ \k -> runProfL k l
--
--  -- but to cocurry, we'd need to be able to 'smuggle information out' in c.
--  cocurry l = nat2 $ \b -> case runNat2 l (ProfL $ \f -> case runNat2 f b of Prof p q -> _uh) of
--    x -> _wat

-- Cat^op -> Prof, Corepresentable, conjoint
data Up f a b = Up { runUp :: f a ~> b }
_Up = dimap runUp Up

instance Category (Hom :: j -> j -> *) => Contravariant (Up :: (i -> j) -> i -> j -> *) where
  contramap f = nat2 $ _Up (. runNat f)

instance (Functor f, Category (Cod f)) => Contravariant (Up f) where
  contramap f = Nat $ _Up (. fmap f)

instance Category (Cod f) => Functor (Up f a) where
  fmap f = _Up (f .)

-- Cat -> Prof, Representable, companion
data Down f a b = Down { runDown :: a ~> f b }
_Down = dimap runDown Down

instance Category (Hom :: i -> i -> *) => Functor (Down :: (j -> i) -> i -> j -> *) where
  fmap f = nat2 $ _Down (runNat f .)

instance Category (Cod f) => Contravariant (Down f) where
  contramap f = Nat $ _Down (. f)

instance (Functor f, Category (Cod f)) => Functor (Down f a) where
  fmap f = _Down (fmap f .)

instance Semimonoidal f => Semimonoidal (Down f a) where
  ap2 (f, g) = Down $ ap2 . (runDown f &&& runDown g)

instance Monoidal f => Monoidal (Down f a) where
  ap0 () = Down $ ap0 . terminal
