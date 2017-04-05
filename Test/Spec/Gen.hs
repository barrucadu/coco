{-# LANGUAGE StrictData #-}

-- |
-- Module      : Test.Spec.Gen
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : StrictData
--
-- Generating well-typed dynamic expressions from smaller components.
--
-- @
-- > :{
-- let baseTerms = [ constant "putMVar_int"  (putMVar  :: MVar Int -> Int -> IO ())
--                 , constant "takeMVar_int" (takeMVar :: MVar Int -> IO Int)
--                 , constant "readMVar_int" (readMVar :: MVar Int -> IO Int)
--                 , constant "succ_int"     (succ     :: Int -> Int)
--                 , variable "x"            (Proxy    :: Proxy Int)
--                 , stateVariable
--                 ] :: [Expr (MVar Int) IO]
-- :}
-- > mapM_ print . (!!8) $ enumerate baseTerms
-- succ_int (succ_int (succ_int (succ_int x)))
-- putMVar_int :state: (succ_int (succ_int x))
-- takeMVar_int :state: >> putMVar_int :state: x
-- takeMVar_int :state: >>= \\x' -> putMVar_int :state: x'
-- readMVar_int :state: >> putMVar_int :state: x
-- readMVar_int :state: >>= \\x' -> putMVar_int :state: x'
-- putMVar_int :state: x >> takeMVar_int :state:
-- putMVar_int :state: x >> readMVar_int :state:
-- @
module Test.Spec.Gen
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

import Test.Spec.Expr


-------------------------------------------------------------------------------
-- Controlled generation

-- | A generator of expressions.
data Generator s m ann = Generator { tiers :: IntMap (Set (Schema s m, ann)), sofar :: Int }
  deriving (Eq, Ord, Show)

-- | Create a new generator from a collection of basic expressions.
newGenerator :: (Monoid ann, Ord ann) => [Schema s m] -> Generator s m ann
newGenerator = newGenerator' . map (\e -> (e, mempty))

-- | Like 'newGenerator', but use an explicit default value.
newGenerator' :: Ord ann => [(Schema s m, ann)] -> Generator s m ann
newGenerator' baseTerms = Generator
  { tiers = merge [M.singleton (exprSize e) (S.singleton s) | s@(e,_) <- baseTerms]
  , sofar = 0
  }

-- | Generate the next tier.
stepGenerator :: (Semigroup ann, Ord ann)
  => (ann -> ann -> Schema s m -> Bool)
  -- ^ Annotation of first expr, annotation of second expr, combined expr.
  -> Generator s m ann -> Generator s m ann
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
getTier :: Int -> Generator s m ann -> Set (Schema s m, ann)
getTier tier = M.findWithDefault S.empty tier . tiers

-- | Apply a function to every expression in a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
mapTier :: Ord ann => ((Schema s m, ann) -> (Schema s m, ann)) -> Int -> Generator s m ann -> Generator s m ann
mapTier = adjustTier . S.map

-- | Filter expressions in a tier.
filterTier :: ((Schema s m, ann) -> Bool) -> Int -> Generator s m ann -> Generator s m ann
filterTier = adjustTier . S.filter

-- | Apply a function to a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
adjustTier :: (Set (Schema s m, ann) -> Set (Schema s m, ann)) -> Int -> Generator s m ann -> Generator s m ann
adjustTier f tier g = g { tiers = M.adjust f tier (tiers g) }

-- | Get the highest size generated so far.
maxTier :: Generator s m ann -> Int
maxTier = sofar


-------------------------------------------------------------------------------
-- Utilities

-- | Merge a list of maps of lists.
merge :: Ord a => [IntMap (Set a)] -> IntMap (Set a)
merge = M.unionsWith S.union
