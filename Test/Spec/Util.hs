{-# LANGUAGE EmptyCase #-}

-- |
-- Module      : Test.Spec.Util
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : EmptyCase
--
-- Utility functions.
module Test.Spec.Util where

import qualified Data.Set as S

-- | A higher-kinded @Void@. This cannot be an 'Applicative' (or a 'Monad').
data Void1 a

instance Functor Void1 where
  fmap _ = absurd1

instance Eq (Void1 a) where
  _ == _ = True

instance Ord (Void1 a) where
  compare _ _ = EQ

instance Read (Void1 a) where
  readsPrec _ _ = []

instance Show (Void1 a) where
  show = absurd1

instance Foldable Void1 where
  foldMap _ = absurd1

instance Traversable Void1 where
  traverse _ = absurd1

-- | Since 'Void1' values don't exist, we use the same trick as for
-- @Void@.
absurd1 :: Void1 a -> b
absurd1 v = case v of {}

-- | Remove duplicates from a list efficiently.
ordNub :: Ord a => [a] -> [a]
ordNub = ordNubOn id

-- | Remove duplicates from a list efficiently.
ordNubOn :: Ord b => (a -> b) -> [a] -> [a]
ordNubOn f = go S.empty where
  go _ [] = []
  go s (x:xs)
    | f x `S.member` s = go s xs
    | otherwise = x : go (S.insert (f x) s) xs

-- | Monadic version of 'mapAccumL' specialised to lists.
mapAccumLM :: Monad m
           => (a -> b -> m (a, c))
           -> a
           -> [b]
           -> m (a, [c])
mapAccumLM _ s []     = pure (s, [])
mapAccumLM f s (x:xs) = do
  (s1, x')  <- f s x
  (s2, xs') <- mapAccumLM f s1 xs
  pure (s2, x' : xs')
