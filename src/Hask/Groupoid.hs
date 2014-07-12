{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2014
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
--------------------------------------------------------------------
module Hask.Groupoid where

import Control.Category
import Hask.Core

-- * Groupoids

class Category c => Groupoid c where
  inverse :: c a b -> c b a

instance Groupoid ((~>) :: j -> j -> *) => Groupoid (Nat :: (i -> j) -> (i -> j) -> *) where
  inverse (Nat f) = Nat (inverse f)

instance (Groupoid ((~>) :: i -> i -> *), Groupoid ((~>) :: j -> j -> *)) =>
  Groupoid (Prod :: (i, j) -> (i, j) -> *) where
  inverse Want = Want
  inverse (Have f g) = Have (inverse f) (inverse g)

instance Groupoid Empty where
  inverse !f = Empty (inverse f)

instance Groupoid Unit where
  inverse Unit = Unit
