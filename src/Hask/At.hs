{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoImplicitPrelude #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2008-2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.At where

import Hask.Core
import Control.Category (Category(..))

-- We can define a functor from the category of natural transformations to Hask
newtype At (x :: i) (f :: i -> *) = At { getAt :: f x }
_At = dimap getAt At

instance Functor (At x) where
  fmap (Nat f) = _At f

instance Semimonoidal (At x) where
  ap2 (At fx, At fy) = At (Lift (fx, fy))

instance Monoidal (At x) where
  ap0 = At . Const

instance Semigroup m => Semigroup (At x m) where
  mult = multM

instance Monoid m => Monoid (At x m) where
  one = oneM

instance Cosemimonoidal (At x) where
  op2 (At (Lift eab))= bimap At At eab

instance Comonoidal (At x) where
  op0 (At (Const x)) = x

instance Cosemigroup m => Cosemigroup (At x m) where
  comult = comultOp

instance Comonoid m => Comonoid (At x m) where
  zero = zeroOp


