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

import Control.DeepSeq (NFData(..))
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, isNothing)
import Data.Semigroup (Semigroup(..))
import Data.Set (Set)
import qualified Data.Set as S
import Test.DejaFu (Failure)

import Test.Spec.Expr (Term)

-- | An annotation on a schema.
--
-- The 'Semigroup' instance is very optimistic, and assumes that
-- combining two schemas will yield the smallest in its new
-- equivalence class (which means there is no unit). It is the job of
-- the refinement-checking to crush these dreams.
data Ann s m x = Ann
  { allResults :: Maybe (Results s m x)
  -- ^ Set of (assignment,results) pairs, or @Nothing@ if
  -- untested. Only tested terms can be checked for refinement. The
  -- first 'Results' set is the results of executing the term with no
  -- interference, the second is the results of executing with
  -- interference.
  , isBackground :: Bool
  -- ^ If the term is entirely composed of background schemas or not.
  , isFailing  :: Bool
  -- ^ If every execution is a failure. Initially, it is assumed a
  -- term is failing if either of its two subterms is, with none of
  -- the base terms failing.
  , isSmallest :: Bool
  -- ^ If this is the smallest observationally-equivalent
  -- term. Initially, it is assumed a term is the smallest.
  , isAtomic   :: Bool
  -- ^ If executing the term is atomic. Initially, it is assumed a
  -- term is not atomic.
  , isBoring   :: Bool
  -- ^ If this term is nonfailing, atomic, and has no effect on the
  -- state. Boring terms are all equivalent, and aren't used when
  -- generating further terms. Initially, it is assumed a term is not
  -- boring.
  }
  deriving (Eq, Ord, Show)

instance Semigroup (Ann s m x) where
  ann1 <> ann2 = Ann
    { allResults   = Nothing
    , isBackground = isBackground ann1 && isBackground ann2
    , isFailing    = isFailing ann1 || isFailing ann2
    , isSmallest   = True
    , isAtomic     = False
    , isBoring     = False
    }

-- | The results of evaluating a schema.
data Results s m x
  = Some (Map (Term s m) (VarResults x, VarResults x))
  -- ^ The schema has some results, with the given variable
  -- assignments. The left results have no interference. The right
  -- results have some. This is used to disambiguate between
  -- equivalences-under-no-interference and
  -- refinements-under-interference: saying two terms are equivalent
  -- is not very useful if that's only the case when there is no
  -- interference!
  | None
  -- ^ The schema has no results (eg, has a function type, has holes).
  deriving (Eq, Ord, Show)

-- | A variable assignment.
data VarAssignment x = VA
  { seedVal :: x
  , varTags :: Map String Int
  } deriving (Eq, Ord, Show)

instance NFData x => NFData (VarAssignment x) where
  rnf (VA s vs) = rnf (s, vs)

-- | Results after assigning values to variables.
type VarResults x = NonEmpty (VarAssignment x, Set (Maybe Failure, x))

-- | The \"default\" annotation.
initialAnn :: Bool -> Ann s m x
initialAnn background = Ann
  { allResults   = Nothing
  , isBackground = background
  , isFailing    = False
  , isSmallest   = True
  , isAtomic     = False
  , isBoring     = False
  }

-- | Update an annotation with expression-evaluation results.
update :: Eq x => Bool -> Results s m x -> Ann s m x -> Ann s m x
update atomic results ann = ann
  { allResults  = Just results
  , isFailing   = case results of { Some rs -> checkIsFailing rs; None -> isFailing ann }
  , isAtomic    = atomic
  , isBoring    = case results of { Some rs -> checkIsBoring atomic rs; None -> isBoring ann }
  }

-- | Check if a set of results corresponds to a failing term.
checkIsFailing :: Map (Term s m) (VarResults x, VarResults x) -> Bool
checkIsFailing results =
  let term_results = M.elems results
      is_failing = isJust . fst
  in all (all (all is_failing . snd) . fst) term_results

-- | Check if a set of results corresponds to a boring term.
checkIsBoring :: Eq x => Bool -> Map (Term s m) (VarResults x, VarResults x) -> Bool
checkIsBoring atomic results = atomic && all (all ch . fst) (M.elems results) where
  ch (va, rs) = all (\(f, x) -> isNothing f && x == seedVal va) rs

-- | Check if the left term (defined by its results) refines the right
-- or the right returns the left.
refines :: Ord x
  => (VarResults x, VarResults x)
  -> (VarResults x, VarResults x)
  -> (Bool, Bool)
refines (nointerfere_a, interfere_a) (nointerfere_b, interfere_b)
    -- if the terms are equivalent, we want to distinguish a
    -- refinement from a "false equivalence" by checking the results
    -- in the presence of interference. we need to use the
    -- uninterfered results to check equivalence/refinement, as
    -- otherwise everything refines everything else: there's always
    -- one result in common, where the interference runs last and so
    -- gives the observation a constant value.
    | are_equiv = check interfere_a interfere_b
    | otherwise = refines_ab_ba
  where
    are_equiv = refines_ab_ba == (True, True)
    refines_ab_ba = check nointerfere_a nointerfere_b

    check rs_a rs_b = foldl' pairAnd (True, True)
      [ (as `S.isSubsetOf` bs, bs `S.isSubsetOf` as)
      | (ass_a, as) <- L.toList rs_a
      , (ass_b, bs) <- L.toList rs_b
      , checkAssigns ass_a ass_b
      ]

    -- two sets of variable assignments match if every variable is
    -- either present in only one execution, or has the same value in
    -- both executions
    --
    -- TODO: this is way too strict currently, it should also consider
    -- alpha-equivalent terms, as the naming of environment variables
    -- is now very arbitrary.
    checkAssigns (VA seed_a vars_a) (VA seed_b vars_b) =
      seed_a == seed_b && M.foldrWithKey (\k v b -> b && M.findWithDefault v k vars_b == v) True vars_a

    pairAnd (a, b) (c, d) = (a && c, b && d)
