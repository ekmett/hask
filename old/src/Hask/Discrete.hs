{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Hask.Discrete where

import Hask.Core

data Discrete a = Discrete a

type instance Hom = (|~>|)

data (|~>|) (x :: Discrete a) (y :: Discrete b) where
  Refl :: x |~>| x

instance Category (|~>|) where
  id = Refl
  Refl . Refl = Refl
