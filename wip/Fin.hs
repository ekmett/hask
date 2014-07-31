{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, LambdaCase #-}
import Control.Applicative
import Control.Monad
import Data.Foldable hiding (elem)
import Data.List (nub)
import Data.Traversable
import Data.Void
import Prelude hiding (all, any, elem)

newtype Fin a = Fin { runFin :: [Monomial a] }
  deriving (Show, Read, Functor, Foldable, Traversable)

data Monomial a 
  = Var a
  | Set (Fin a)
  deriving (Show, Read, Functor, Foldable, Traversable)

reduce :: Eq a => Fin a -> Fin a
reduce (Fin xs) = Fin $ nub (mon <$> xs) where
  mon (Set xs) = Set (reduce xs)
  mon x = x

null :: Fin a -> Bool
null (Fin xs) = Prelude.null xs

size :: Eq a => Fin a -> Int
size xs = size (reduce xs)

elem :: Eq a => Fin a -> Fin a -> Bool
elem xs = any (Set xs ==) . runFin

set :: Fin a -> Fin a
set xs = Fin [Set xs]

instance Eq a => Eq (Fin a) where
  Fin xs == Fin ys = all (\x -> any (== x) ys) xs
                  && all (\y -> any (== y) xs) ys

instance Applicative Fin where
  pure a = Fin [Var a]
  (<*>) = ap

instance Alternative Fin where
  empty = Fin []
  Fin xs <|> Fin ys = Fin (xs ++ ys)

instance Monad Fin where
  return a = Fin [Var a]
  Fin m >>= f = Fin $ m >>= \ case
    Var a     -> runFin (f a)
    Set m     -> [Set (m >>= f)]

instance MonadPlus Fin where
  mzero = empty
  mplus = (<|>) 

instance Eq a => Eq (Monomial a) where
  Var a == Var b = a == b
  Set a == Set b = a == b

-- countable if made up of all initial elements
countables :: Fin a -> Maybe [a]
countables (Fin xs) = traverse (\ case Var g -> Just g; _ -> Nothing) xs

{-
-- not a traversal
leaves :: Applicative m => ([a] -> m (Fin a)) -> Fin a -> m (Fin a)
leaves k = fin where
  fin xs = case counts xs of
    Just ys -> k ys
    Nothing -> traverse mon xs
  mon (Set xs) = Set <$> leaves k xs
  mon m        = pure m
-}
