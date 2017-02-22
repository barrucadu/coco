{-# LANGUAGE StrictData #-}

-- |
-- Module      : Test.Spec.Ann
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : StrictData
--
-- Expression annotations.
module Test.Spec.Ann where

import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.Semigroup (Semigroup(..))
import Data.Set (Set)
import qualified Data.Set as S
import Test.DejaFu (Failure)

import Test.Spec.Expr (Expr, exprSize)
import Test.Spec.Gen (Generator, mapTier)

-- | An annotation on an expression.
--
-- The 'Semigroup' instance is very optimistic, and assumes that
-- combining two expressions will yield the smallest in its new
-- equivalence class (which means there is no unit). It is the job of
-- the refinement-checking to crush these dreams.
data Ann x = Ann
  { allResults :: Maybe (Results x)
  -- ^ Set of (assignment,results) pairs, or @Nothing@ if
  -- untested. Only tested terms can be checked for refinement.
  , isFailing  :: Bool
  -- ^ If every execution is a failure. Initially, it is assumed a
  -- term is failing if either of its two subterms is, with none of
  -- the base terms failing.
  , isSmallest :: Bool
  -- ^ If this is the smallest observationally-equivalent
  -- term. Initially, it is assumed a term is the smallest.
  , isBoring   :: Bool
  -- ^ If this term is nonfailing, atomic, and has no effect on the
  -- state. Boring terms are all equivalent, and aren't used when
  -- generating further terms. Initially, it is assumed a term is not
  -- boring.
  }
  deriving (Eq, Ord, Show)

instance Semigroup (Ann x) where
  ann1 <> ann2 = Ann { allResults = Nothing
                     , isFailing  = isFailing ann1 || isFailing ann2
                     , isSmallest = True
                     , isBoring   = False
                     }

-- | The results of evaluating an expression.
data Results x
  = Some (NonEmpty (VarAssignment, Set (Maybe Failure, x)))
  -- ^ The expression has some results, with the given variable
  -- assignments.
  | None
  -- ^ The expression has no results (eg, has a function type, has
  -- free variables).
  deriving (Eq, Ord, Show)

-- | A variable assignment.
data VarAssignment = VA
  { seedTag :: Int
  , varTags :: Map String Int
  } deriving (Eq, Ord, Show)

-- | The \"default\" annotation. This is not the unit of
-- 'Semigroup.<>', as it has no unit.
initialAnn :: Ann x
initialAnn = Ann
  { allResults = Nothing
  , isFailing  = False
  , isSmallest = True
  , isBoring   = False
  }

-- | Annotate an expression.
annotate :: Expr s m -> ann -> Generator s m ann -> Generator s m ann
annotate expr ann = mapTier go (exprSize expr) where
  go (ann0, expr0) = (if expr0 == expr then ann else ann0, expr0)

-- | Update an annotation with expression-evaluation results.
update :: Maybe (NonEmpty (VarAssignment, Set (Maybe Failure, x))) -> Ann x -> Ann x
update Nothing ann = ann { allResults = Just None }
update (Just results) ann = ann
  { allResults  = Just (Some results)
  , isFailing   = all (all (isJust . fst) . snd) results
  }

-- | Check if the left expression refines the right or the right returns the left.
--
-- If either annotation is missing results, @Nothing@ is returned. If
-- either annotation has no results (which is different to missing
-- results!), @(False, False)@ is returned.
refines :: Ord x => Ann x -> Ann x -> Maybe (Bool, Bool)
refines ann_a ann_b = check <$> allResults ann_a <*> allResults ann_b where
  check (Some results_a) (Some results_b) = foldl' pairAnd (True, True)
    [ (as `S.isSubsetOf` bs, bs `S.isSubsetOf` as)
    | (ass_a, as) <- L.toList results_a
    , (ass_b, bs) <- L.toList results_b
    , checkAssigns ass_a ass_b
    ]
  check _ _ = (False, False)

  -- two sets of variable assignments match if every variable is
  -- either present in only one execution, or has the same value in
  -- both executions
  checkAssigns (VA seed_a vars_a) (VA seed_b vars_b) =
    seed_a == seed_b && M.foldrWithKey (\k v b -> b && M.findWithDefault v k vars_b == v) True vars_a

  pairAnd (a, b) (c, d) = (a && c, b && d)
