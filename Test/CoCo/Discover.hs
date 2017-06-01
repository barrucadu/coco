{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Test.CoCo.Discover
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : MonoLocalBinds, ScopedTypeVariables, TupleSections
--
-- Discover observational equalities and refinements between
-- concurrent functions.
module Test.CoCo.Discover where

import           Control.Arrow      (first, second)
import           Control.DeepSeq    (NFData)
import           Data.Foldable      (toList)
import           Data.Function      (on)
import qualified Data.List.NonEmpty as L
import qualified Data.Map.Strict    as M
import           Data.Maybe         (fromJust, mapMaybe)
import           Data.Proxy         (Proxy(..))
import qualified Data.Set           as S
import qualified Data.Typeable      as T

import           Test.CoCo.Ann
import           Test.CoCo.Eval     (runSingle)
import           Test.CoCo.Expr     (Schema, Term, environment, exprTypeRep,
                                     findInstance, unBind)
import           Test.CoCo.Gen      (Generator, adjustTier, getTier,
                                     newGenerator, stepGenerator)
import           Test.CoCo.Logic
import           Test.CoCo.Sig      (Sig(..), complete)
import           Test.CoCo.Type     (fromDyn)
import           Test.CoCo.TypeInfo (TypeInfo(..), getVariableBaseName)
import           Test.CoCo.Util

-- | Attempt to discover properties of the given set of concurrent
-- operations. Returns three sets of observations about, respectively:
-- the first set of expressions; the second set of expressions; and
-- the combination of the two.
discover :: forall s1 s2 o x. (NFData o, NFData x, Ord o, Ord x, T.Typeable s1, T.Typeable s2, T.Typeable x)
  => [(T.TypeRep, TypeInfo)]
  -- ^ Information about types. There MUST be an entry for every hole and seed type!
  -> [(String, x -> Bool)]
  -- ^ Predicates on the seed value. Used to discover properties which
  -- only hold with certain seeds.
  -> Sig s1 o x
  -- ^ A collection of expressions
  -> Sig s2 o x
  -- ^ Another collection of expressions.
  -> Int
  -- ^ Term size limit
  -> ([Observation], [Observation], [Observation])
discover typeInfos seedPreds sig1 sig2 =
  case lookup (T.typeRep (Proxy :: Proxy x)) typeInfos of
    Just tyI ->
      let seeds = mapMaybe fromDyn (listValues tyI)
      in discoverWithSeeds typeInfos seedPreds sig1 sig2 seeds
    Nothing  -> \_ -> ([], [], [])

-- | Like 'discover', but takes a list of seeds.
discoverWithSeeds :: (NFData o, NFData x, Ord o, Ord x, T.Typeable s1, T.Typeable s2)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Sig s1 o x
  -> Sig s2 o x
  -> [x]
  -> Int
  -> ([Observation], [Observation], [Observation])
discoverWithSeeds typeInfos seedPreds sig1 sig2 seeds lim =
    let
      (g1, obs1) = discoverSingleWithSeeds' typeInfos seedPreds sig1 seeds lim
      (g2, obs2) = discoverSingleWithSeeds' typeInfos seedPreds sig2 seeds lim
      obs3       = crun (findObservations g1 g2 0)
    in (obs1, obs2, obs3)
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g1 g2 = go where
      go tier =
        let exprs = getTier tier g1
            smallers = map (`getTier` g2) [0..tier]
            (_, observations) = observe seedPreds varfun (\_ _ -> False) smallers exprs
        in cappend observations $ if tier == lim then cnil else go (tier+1)

    -- get the base name for a variable
    varfun = getVariableBaseName typeInfos


-- | Like 'discover', but only takes a single set of expressions. This
-- will lead to better pruning.
discoverSingle :: forall s o x. (NFData o, NFData x, Ord o, Ord x, T.Typeable s, T.Typeable x)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Sig s o x
  -> Int
  -> [Observation]
discoverSingle typeInfos seedPreds sig =
  case lookup (T.typeRep (Proxy :: Proxy x)) typeInfos of
    Just tyI ->
      let seeds = mapMaybe fromDyn (listValues tyI)
      in discoverSingleWithSeeds typeInfos seedPreds sig seeds
    Nothing  -> \_ -> []

-- | Like 'discoverSingle', but takes a list of seeds.
discoverSingleWithSeeds :: (NFData o, NFData x, Ord o, Ord x, T.Typeable s)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Sig s o x
  -> [x]
  -> Int
  -> [Observation]
discoverSingleWithSeeds typeInfos seedPreds sig seeds =
  snd . discoverSingleWithSeeds' typeInfos seedPreds sig seeds

-- | Like 'discoverSingleWithSeeds', but returns the generator.
discoverSingleWithSeeds' :: forall s o x. (NFData o, NFData x, Ord o, Ord x, T.Typeable s)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Sig s o x
  -> [x]
  -> Int
  -> (Generator s o x, [Observation])
discoverSingleWithSeeds' typeInfos seedPreds sig seeds lim =
    let sigc = complete sig
        g = newGenerator typeInfos
                         ([(e, initialAnn False) | e <- expressions           sigc] ++
                          [(e, initialAnn True)  | e <- backgroundExpressions sigc])
    in second crun $ findObservations g 0
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g tier =
      let evaled = map evalSchema . S.toList $ getTier tier g
          smallers = map (`getTier` g) [0..tier-1]
          (kept, observations) = first crun (observe seedPreds varfun ((==) `on` exprTypeRep) smallers evaled)
          g' = adjustTier (const (S.fromList kept)) tier g
      in second (cappend observations) $
         if tier == lim
         then (g', cnil)
         else findObservations (stepGenerator checkNewTerm g') (tier+1)

    -- evaluate all terms of a schema and store their results
    evalSchema (schema, (_, ann)) = case theTerms ann of
      (mostGeneralTerm:rest) ->
        let mresult = evalTerm mostGeneralTerm
            new_ann = case mresult of
              Just (atomic, no_interference, interference) ->
                let getResults = getResultsFrom mostGeneralTerm
                    resultsOf t = (\r1 r2 -> (t, (r1, r2))) <$> getResults no_interference t <*> getResults interference t
                    results      = mapMaybe resultsOf rest
                    all_results  = (mostGeneralTerm, (no_interference, interference)) : results
                in update atomic (Some all_results) ann
              Nothing -> update False None ann
        in (schema, (Just ann, new_ann))
      [] -> (schema, (Just ann, update False None ann))

    -- evaluate a term
    evalTerm term =
      let maybe_no_interference = run False term
          maybe_interference    = run True  term
      in do
        (atomic, no_interference) <- maybe_no_interference
        (_,      interference)    <- maybe_interference
        pure (atomic, no_interference, interference)

    -- evaluate a term with optional interference
    run :: Bool -> Term s -> Maybe (Bool, VarResults o x)
    run interference term =
      runSingle typeInfos
                (initialState sig)
                (if interference then Just (setState sig) else Nothing)
                (observation sig)
                (backToSeed sig)
                seeds
                term

    -- get the base name for a variable
    varfun = getVariableBaseName typeInfos

-- | Get the results of a more specific term from a more general one
getResultsFrom
  :: Term s         -- ^ The general term.
  -> VarResults o x -- ^ Its results.
  -> Term s         -- ^ The specific term.
  -> Maybe (VarResults o x)
getResultsFrom generic results specific = case findInstance generic specific of
    Just nameMap -> L.nonEmpty $ mapMaybe (juggleVariables nameMap) (toList results)
    Nothing -> Nothing
  where
    -- attempt to rearrange the variable assignment of this result
    -- into the form required by the more specific term.
    juggleVariables nameMap (va, rs) = go (map fst $ environment specific) M.empty where
      -- eliminate specific variables one at a time, checking that the
      -- variable assignment is consistent with them all being equal.
      go (s:ss) vts = case lookup s nameMap of
        Just (g:gs) ->
          let gv = fromJust (M.lookup g (varTags va))
          in if all (\g' -> M.lookup g' (varTags va) == Just gv) gs
             then go ss (M.insert s gv vts)
             else Nothing
        _ -> Nothing
      go [] vts = Just (VA (seedVal va) vts, rs)


-------------------------------------------------------------------------------
-- Utilities

-- | Filter for term generation: only generate out of non-neutral
-- terms; and only generate binds out of smallest terms.
checkNewTerm :: Ann s o x -> Ann s o x -> Schema s -> Bool
checkNewTerm ann1 ann2 expr
  | isNeutral ann1 || isNeutral ann2 = False
  | otherwise = case unBind expr of
      Just ([], _, _) -> isSmallest ann1 && isSmallest ann2
      Just _ -> isSmallest ann2
      _ -> True
