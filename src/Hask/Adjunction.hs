{-# LANGUAGE PolyKinds, KindSignatures, MultiParamTypeClasses, FunctionalDependencies, TypeFamilies, TypeOperators #-}
module Hask.Adjunction 
  ( (-|)(..)
  , swap
  , Curried(..)
  ) where

import Hask.Category
import Hask.Get
import qualified Prelude

--------------------------------------------------------------------------------
-- * Adjunctions
--------------------------------------------------------------------------------

class (Functor f, Functor g, Dom f ~ Cod g, Cod g ~ Dom f) => (f :: j -> i) -| (g :: i -> j) | f -> g, g -> f where
  adj :: Iso (->) (->) (->) (Cod f (f a) b) (Cod f (f a') b') (Cod g a (g b)) (Cod g a' (g b'))

instance (,) e -| (->) e where
  adj = dimap (. swap) (. swap) . curried

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

--------------------------------------------------------------------------------
-- * Currying
--------------------------------------------------------------------------------

class (Bifunctor p, Bifunctor q) => Curried (p :: k -> i -> j) (q :: i -> j -> k) | p -> q, q -> p where
  curried :: Iso (->) (->) (->)
    (Dom2 p (p a b) c) (Dom2 p (p a' b') c')
    (Dom2 q a (q b c)) (Dom2 q a' (q b' c'))

instance Curried (,) (->) where
  curried = dimap Prelude.curry Prelude.uncurry
