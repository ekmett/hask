{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
module Hask.Colim where

import Control.Category (Category(..))
import Data.Constraint (Dict(Dict))
import Hask.Core
import Prelude (($))

class (k ~ (~>)) => Cocomplete (k :: j -> j -> *) where
  type Colim :: (i -> j) -> j

  colim :: k (f a) (Colim f)

  -- The explicit witness here allows us to quantify over all kinds i.
  -- Colim -| Const
  cocomplete :: Dict ((Colim :: (i -> j) -> j) -| Const)
  default cocomplete :: ((Colim :: (i -> j) -> j) -| Const) => Dict ((Colim :: (i -> j) -> j) -| Const)
  cocomplete = Dict

-- * @(->)@ is cocomplete

data Colim1 (f :: i -> *) where
  Colim :: f x -> Colim1 f

instance Functor Colim1 where
  fmap (Nat f) (Colim g)= Colim (f g)

instance Cosemimonoidal Colim1 where
  op2 (Colim (Lift ab)) = bimap Colim Colim ab

instance Comonoidal Colim1 where
  op0 (Colim (Const a)) = a

instance Cosemigroup m => Cosemigroup (Colim1 m) where
  comult = comultOp

instance Comonoid m => Comonoid (Colim1 m) where
  zero = zeroOp

instance Colim1 -| Const1 where
  adj = dimap (\f -> Nat $ Const . f . Colim) $ \(Nat g2cb) (Colim g) -> getConst (g2cb g)

instance Cocomplete (->) where
  type Colim = Colim1
  colim = Colim

-- * The cocompletion of @(j -> *)@ borrows its structure from @*@

data Colim2 (f :: i -> j -> *) (x :: j) where
  Colim2 :: f y x -> Colim2 f x

instance Functor Colim2 where
  fmap f = Nat $ \(Colim2 g) -> Colim2 (runNat (runNat f) g)

instance Colim2 -| Const2 where
  adj = dimap (\(Nat f) -> nat2 $ Const2 . f . Colim2) $
               \ f -> Nat $ \ xs -> case xs of
                 Colim2 fyx -> getConst2 $ runNat2 f fyx

instance Cocomplete (Nat :: (i -> *) -> (i -> *) -> *) where
  type Colim = Colim2
  colim = Nat Colim2
