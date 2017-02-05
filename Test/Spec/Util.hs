{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}

-- |
-- Module      : Test.Spec.Util
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : DeriveGeneric, EmptyCase
--
-- Utility functions.
module Test.Spec.Util where

import Control.Exception (Exception)
import Data.Data (Data(..))
import Data.Ix (Ix(..))
import Data.Maybe (fromJust, isJust)
import Data.Semigroup (Semigroup(..))
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import Language.Haskell.TH.Syntax (Type(AppT))
import GHC.Generics (Generic)

-- | A higher-kinded @Void@. This cannot be an 'Applicative' (or a 'Monad').
data Void1 a deriving Generic

instance Typeable a => Data (Void1 a) where
  gunfold _ _ _ = error "invalid constructor"
  toConstr = absurd1
  dataTypeOf = absurd1

instance Ix (Void1 a) where
  range     _ = []
  index     _ = absurd1
  inRange   _ = absurd1
  rangeSize _ = 0

instance Typeable a => Exception (Void1 a)

instance Eq        (Void1 a) where _ == _        = True
instance Ord       (Void1 a) where compare _ _   = EQ
instance Read      (Void1 a) where readsPrec _ _ = []
instance Semigroup (Void1 a) where a <> _        = a
instance Show      (Void1 a) where show          = absurd1

instance Functor     Void1 where fmap _     = absurd1
instance Foldable    Void1 where foldMap _  = absurd1
instance Traversable Void1 where traverse _ = absurd1

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

-- | 'mapMaybe' over a set.
smapMaybe :: Ord b => (a -> Maybe b) -> Set a -> Set b
smapMaybe f = S.map fromJust . S.filter isJust . S.map f

-- | Turn an 'Either' into a 'Maybe'.
eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe = either (const Nothing) Just

-- | Remove a 'Maybe', throwing the given error on @Nothing@.
unmaybe :: String -> Maybe a -> a
unmaybe str Nothing = error str
unmaybe _ (Just a) = a

-- | Shove a 'Maybe' into another monad.
shoveMaybe :: Monad m => Maybe (m a) -> m (Maybe a)
shoveMaybe = maybe (pure Nothing) (fmap Just)

-- | Get the constructor of a TH type.
constr :: Type -> Type
constr (AppT ty _) = constr ty
constr ty = ty
