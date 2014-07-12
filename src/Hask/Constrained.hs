{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wall #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Constrained where

-- import Control.Category (Category(..))
import Data.Constraint ((:-)(Sub), (\\), Dict(Dict))
import Hask.Core
import Hask.Rep
import Prelude (($))

infixr |=

-- |
-- @(|=) :: Constraint -> * -> *@
--
-- This is a corepresentable profunctor
newtype p |= q = Constrained { runConstrained :: p => q }

instance Contravariant (|=) where
  contramap ab = Nat $ \bc -> Constrained $ case ab of
    Sub Dict -> runConstrained bc

instance Functor ((|=) e) where
  fmap bc ab = Constrained $ bc (runConstrained ab)

instance Semimonoidal ((|=) e) where
  ap2 (ea,eb) = Constrained $ (runConstrained ea, runConstrained eb)

instance Monoidal ((|=) e) where
  ap0 () = Constrained ()

instance Semimonad ((|=) e) where
  join cc = Constrained (runConstrained (runConstrained cc))

instance Semigroup p => Semigroup (e |= p) where
  mult = multM

instance Monoid p => Monoid (e |= p) where
  one = oneM

instance Cosemimonad ((|=) e) where
  duplicate cc = Constrained cc

instance Monoid e => Comonad ((|=) e) where
  extract cc = runConstrained cc \\ (one :: () :- e)

instance Corepresentable (|=) where
  type Corep (|=) = Dict
  _Corep = dimap (\ab Dict -> case ab of Constrained b -> b) (\ab -> Constrained $ ab Dict)

-- | We could flip this around to permit a @Curried@ instance, but then we lose a lot of structure.
data EnvC p q = EnvC (Dict p) q

-- EnvC p (Either a b) -> Either (EnvC p a) (EnvC p b)

instance Functor EnvC where
  fmap f = Nat $ \(EnvC p q) -> EnvC (fmap f p) q

instance Functor (EnvC p) where
  fmap f (EnvC p q) = EnvC p (f q)

instance Cosemimonad (EnvC p) where
  duplicate q@(EnvC p _) = EnvC p q

instance Comonad (EnvC p) where
  extract (EnvC _ q) = q

instance Cosemimonoidal (EnvC p) where
  op2 (EnvC p eab) = bimap (EnvC p) (EnvC p) eab

instance Comonoidal (EnvC p) where
  op0 (EnvC _ v) = v

-- all constraints are semimonoids
instance Semimonoidal (EnvC p) where
  ap2 (EnvC Dict p, EnvC Dict q) = EnvC Dict (p, q)

instance Monoid p => Monoidal (EnvC p) where
  ap0 = EnvC (Dict \\ (one :: () :- p))

instance Semimonad (EnvC p) where
  join (EnvC Dict p) = p

instance EnvC e -| (|=) e where
  adj = dimap (\eab a -> Constrained $ eab (EnvC Dict a))
              (\aeb (EnvC Dict a) -> runConstrained (aeb a))
