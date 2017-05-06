{-# LANGUAGE StrictData #-}

-- |
-- Module      : Test.CoCo.Gen
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : StrictData
--
-- Generating well-typed dynamic expressions from smaller components.
module Test.CoCo.Gen
  ( -- * Generating Terms
    Generator
  , newGenerator
  , newGenerator'
  , stepGenerator
  , getTier
  , mapTier
  , filterTier
  , adjustTier
  , maxTier
  ) where

import Control.Monad (filterM)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M
import Data.Maybe (maybeToList)
import Data.Semigroup (Semigroup, (<>))
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

import Test.CoCo.Expr


-------------------------------------------------------------------------------
-- Controlled generation

-- | A generator of expressions.
data Generator s ann = Generator { tiers :: IntMap (Set (Schema s, ann)), sofar :: Int }
  deriving (Eq, Ord, Show)

-- | Create a new generator from a collection of basic expressions.
newGenerator :: (Monoid ann, Ord ann) => [Schema s] -> Generator s ann
newGenerator = newGenerator' . map (\e -> (e, mempty))

-- | Like 'newGenerator', but use an explicit default value.
newGenerator' :: Ord ann => [(Schema s, ann)] -> Generator s ann
newGenerator' baseTerms = Generator
  { tiers = merge [M.singleton (exprSize e) (S.singleton s) | s@(e,_) <- baseTerms]
  , sofar = 0
  }

-- | Generate the next tier.
stepGenerator :: (Semigroup ann, Ord ann, Typeable s)
  => (ann -> ann -> Schema s -> Bool)
  -- ^ Annotation of first expr, annotation of second expr, combined expr.
  -> Generator s ann -> Generator s ann
stepGenerator check g = Generator newTiers (sofar g + 1) where
  newTiers = merge
    [ tiers g
    , M.singleton (sofar g + 1) funAps
    , M.singleton (sofar g + 1) binds
    ]

  -- produce new terms by function application.
  funAps = mkTerms 0 $ \terms candidates ->
    [ (new, fAnn <> eAnn)
      | (f, fAnn) <- terms
      , (e, eAnn) <- candidates
      , new <- maybeToList (f $$ e)
      , check fAnn eAnn new
    ]

  -- produce new terms by monad-binding variables.
  binds = mkTerms 1 $ \terms candidates ->
    [ (new, bAnn <> eAnn)
      | (b, bAnn) <- terms
      -- don't allow a binder which is a hole
      , not (isHole b)
      , (e, eAnn) <- candidates
      , holeset <- powerset . map fst $ holes e
      , new <- maybeToList (bind holeset b e)
      , check bAnn eAnn new
    ]

  -- produce new terms
  mkTerms n f = M.foldMapWithKey go (tiers g) where
    go tier terms = S.fromList $
      let candidates = getTier (sofar g + 1 - tier - n) g
      in f (S.toList terms) (S.toList candidates)

  powerset = filterM (const [False,True])

-- | Get the terms of a given size.
getTier :: Int -> Generator s ann -> Set (Schema s, ann)
getTier tier = M.findWithDefault S.empty tier . tiers

-- | Apply a function to every expression in a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
mapTier :: Ord ann => ((Schema s, ann) -> (Schema s, ann)) -> Int -> Generator s ann -> Generator s ann
mapTier = adjustTier . S.map

-- | Filter expressions in a tier.
filterTier :: ((Schema s, ann) -> Bool) -> Int -> Generator s ann -> Generator s ann
filterTier = adjustTier . S.filter

-- | Apply a function to a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
adjustTier :: (Set (Schema s, ann) -> Set (Schema s, ann)) -> Int -> Generator s ann -> Generator s ann
adjustTier f tier g = g { tiers = M.adjust f tier (tiers g) }

-- | Get the highest size generated so far.
maxTier :: Generator s ann -> Int
maxTier = sofar


-------------------------------------------------------------------------------
-- Utilities

-- | Merge a list of maps of lists.
merge :: Ord a => [IntMap (Set a)] -> IntMap (Set a)
merge = M.unionsWith S.union
