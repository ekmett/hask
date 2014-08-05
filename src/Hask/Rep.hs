{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
module Hask.Rep where

import Hask.Core
import Hask.Prof

-- * Representability

class Representable (p :: x -> y -> z) where
  type Rep p :: y -> x
  _Rep :: Iso (p a b) (p a' b') (Hom a (Rep p b)) (Hom a' (Rep p b'))

instance Representable (->) where
  type Rep (->) = Id
  _Rep = un (mapping _Id)

instance Representable (Nat :: (i -> *) -> (i -> *) -> *) where
  type Rep (Nat :: (i -> *) -> (i -> *) -> *) = Id
  _Rep = un (mapping _Id)

instance Representable (:-) where
  type Rep (:-) = Id
  _Rep = un (mapping _Id)

instance Representable (Down f) where
  type Rep (Down f) = f
  _Rep = dimap runDown Down

instance ( Representable p
         , Representable q
         , Composed (Hom :: i -> i -> *)
         , Functor (Rep q)
         , Category (Hom :: i -> i -> *)
         , Category (Hom :: j -> j -> *)
         ) => Representable (Prof (p :: j -> k -> *) (q :: i -> j -> *)) where
  type Rep (Prof p q) = Rep q ∘ Rep p
  _Rep = dimap (\(Prof p q) -> compose . fmap (get _Rep p) . get _Rep q)
               (\k -> Prof (beget _Rep id) (beget _Rep (decompose . k)))

{-
downs = dimap hither yon where
  hither (Prof (Down xgc) (Down dfx)) = Down (Compose . fmap xgc . dfx)
  yon (Down dfgc) = Prof (Down id) (Down (getCompose . dfgc))
-}

class Corepresentable (p :: x -> y -> z) where
  type Corep p :: x -> y
  _Corep :: Iso (p a b) (p a' b') (Hom (Corep p a) b) (Hom (Corep p a') b')

instance Corepresentable (->) where
  type Corep (->) = Id
  _Corep = lmapping _Id

instance Corepresentable (Nat :: (i -> *) -> (i -> *) -> *) where
  type Corep (Nat :: (i -> *) -> (i -> *) -> *) = Id
  _Corep = lmapping _Id

instance Corepresentable (:-) where
  type Corep (:-) = Id
  _Corep = lmapping _Id

instance Corepresentable (Up f) where
  type Corep (Up f) = f
  _Corep = dimap runUp Up

instance ( Corepresentable p
         , Corepresentable q
         , Composed (Hom :: k -> k -> *)
         , Functor (Corep p)
         , Category (Hom :: j -> j -> *)
         , Category (Hom :: k -> k -> *)
         ) => Corepresentable (Prof (p :: j -> k -> *) (q :: i -> j -> *)) where
  type Corep (Prof p q) = Corep p ∘ Corep q
  _Corep = dimap (\(Prof p q) -> get _Corep p . fmap (get _Corep q) . decompose)
                 (\k -> Prof (beget _Corep (k . compose)) (beget _Corep id))

instance Corepresentable (|-) where
  type Corep (|-) = IdC
  _Corep = lmapping _Id


{-
ups = dimap hither yon where
  hither (Prof (Up gxc) (Up fdx)) = Up (gxc . fmap fdx . getCompose)
  yon (Up dgfc) = Prof (Up (dgfc . Compose)) (Up id)
-}

-- | Cat^op -> Prof, Corepresentable, conjoint
data Up f a b = Up { runUp :: f a ~> b }
_Up = dimap runUp Up

instance Category (Hom :: j -> j -> *) => Contravariant (Up :: (i -> j) -> i -> j -> *) where
  contramap f = nat2 $ _Up (. transport f)

instance (Functor f, Category (Cod f)) => Contravariant (Up f) where
  contramap f = Nat $ _Up (. fmap f)

instance Category (Cod f) => Functor (Up f a) where
  fmap f = _Up (f .)

instance Precartesian (Cod f) => Semimonoidal (Up f a) where
  ap2 (f, g) = Up $ runUp f &&& runUp g

instance (Precartesian (Cod f), Semigroup b) => Semigroup (Up f a b) where
  mult = multM

instance (Cartesian (Cod f), Monoid b) => Monoid (Up f a b) where
  one = oneM

instance Cartesian (Cod f) => Monoidal (Up f a) where
  ap0 () = Up terminal

instance Semimonad (Up f a) where
  join k = Up $ \a -> runUp (runUp k a) a

-- instance Cartesian (Cod f) => Semimonad (Up f a) where
--  join (Up f) = TODO

-- | Cat -> Prof, Representable, companion
data Down f a b = Down { runDown :: a ~> f b }
_Down = dimap runDown Down

instance Category (Hom :: i -> i -> *) => Functor (Down :: (j -> i) -> i -> j -> *) where
  fmap f = nat2 $ _Down (transport f .)

instance Category (Cod f) => Contravariant (Down f) where
  contramap f = Nat $ _Down (. f)

instance (Functor f, Category (Cod f)) => Functor (Down f a) where
  fmap f = _Down (fmap f .)

instance Semimonoidal f => Semimonoidal (Down f a) where
  ap2 (f, g) = Down $ ap2 . (runDown f &&& runDown g)

instance Monoidal f => Monoidal (Down f a) where
  ap0 () = Down $ ap0 . terminal

instance Semimonad f => Semimonad (Down f a) where
  join f = Down $ \r -> join $ fmap (\g -> runDown g r) $ runDown f r

instance (Semimonoidal f, Semigroup b) => Semigroup (Down f a b) where
  mult = multM

instance (Monoidal f, Monoid b) => Monoid (Down f a b) where
  one = oneM
