{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : Test.CoCo.Util
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : RankNTypes
--
-- Utility functions.
module Test.CoCo.Util where

import           Data.Maybe                 (fromJust, isJust)
import           Data.Set                   (Set)
import qualified Data.Set                   as S
import           Language.Haskell.TH.Syntax (Type(AppT))

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

-- | Discard elements from a list which match a predicate against some
-- earlier value.
discardLater :: (a -> a -> Bool) -> [a] -> [a]
discardLater p = go where
  go (x:xs) = x : go (filter (not . p x) xs)
  go [] = []


-------------------------------------------------------------------------------
-- * Church-encoded lists

-- | Church-encoded lists.
newtype ChurchList a = CL (forall r. (a -> r -> r) -> r -> r)

instance Show a => Show (ChurchList a) where
  show = show . crun

-- | @[]@ for Church-encoded lists.
cnil :: ChurchList a
cnil = CL (\_ n -> n)

-- | @:@ for Church-encoded lists.
ccons :: a -> ChurchList a -> ChurchList a
ccons x (CL xs) = CL (\c n -> c x (xs c n))

-- | Snoc for Church-encoded lists.
csnoc :: ChurchList a -> a -> ChurchList a
csnoc xs x = cappend xs (ccons x cnil)

-- | @++@ for Church-encoded lists.
cappend :: ChurchList a -> ChurchList a -> ChurchList a
cappend (CL xs) (CL ys) = CL (\c n -> xs c (ys c n))

-- | Convert a Church-encoded list to a regular list.
crun :: ChurchList a -> [a]
crun (CL xs) = xs (:) []
