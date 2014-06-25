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
--------------------------------------------------------------------
module Hask.Colim where

import qualified Control.Applicative as Base
import qualified Control.Arrow as Arrow
import Control.Category (Category(..))
import qualified Data.Constraint as Constraint
import Data.Constraint ((:-)(Sub), (\\), Dict(Dict))
import qualified Data.Foldable as Base
import qualified Data.Functor as Base
import qualified Data.Functor.Identity as Base
import qualified Data.Monoid as Base
import Data.Proxy
import Data.Tagged
import qualified Data.Traversable as Base
import Data.Void
import Hask.Core
import qualified Prelude
import Prelude (Either(..), ($), either, Bool, undefined, Maybe(..))
import GHC.Exts (Constraint, Any)
import Unsafe.Coerce (unsafeCoerce)

type family Colim :: (i -> j) -> j
type instance Colim = Colim1
type instance Colim = Colim2

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

data Colim2 (f :: i -> j -> *) (x :: j) where
  Colim2 :: f y x -> Colim2 f x

instance Functor Colim2 where
  fmap f = Nat $ \(Colim2 g) -> Colim2 (runNat (runNat f) g)

-- instance Comonoidal Colim2
-- instance Comonoid m => Comonoid (Colim1 m)

instance Colim2 -| Const2 where
  adj = dimap (\(Nat f) -> nat2 $ Const2 . f . Colim2) $
               \ f -> Nat $ \ xs -> case xs of
                 Colim2 fyx -> getConst2 $ runNat2 f fyx

--class ColimC (f :: i -> Constraint) where
--  colimDict :: Colim (Up f Dict)
--    p (f a) :- ColimC f

class k ~ (~>) => Cocomplete (k :: j -> j -> *) where
  -- The explicit witness here allows us to quantify over all kinds i.
  -- Colim -| Const
  cocomplete :: () :- ((Colim :: (i -> j) -> j) -| Const)
  default cocomplete :: ((Colim :: (i -> j) -> j) -| Const) => () :- ((Colim :: (i -> j) -> j) -| Const)
  cocomplete = Sub Dict

instance Cocomplete (->)
instance Cocomplete (Nat :: (i -> *) -> (i -> *) -> *)
-- instance Cocomplete (Nat :: (i -> j -> *) -> (i -> j -> *) -> *)
-- instance Cocomplete ((:-) :: Constraint -> Constraint -> *)
