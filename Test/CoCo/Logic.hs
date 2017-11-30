{-# LANGUAGE GADTs #-}

-- |
-- Module      : Test.CoCo.Logic
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs
--
-- Observations and stuff about them.
module Test.CoCo.Logic where

import           Control.Arrow    (second)
import           Data.List        (foldl', sortOn)
import           Data.Maybe       (isJust, isNothing)
import           Data.Typeable    (TypeRep, Typeable)

import           Test.CoCo.Ann    (Ann(..), Results(..), VarResults, refines)
import           Test.CoCo.Expr   (Term, eq, exprSize, isInstanceOf, rename)
import           Test.CoCo.Rename (Projection, isMoreGeneralThan, projections,
                                   renaming)
import           Test.CoCo.Util   (ChurchList, cappend, cnil, csnoc,
                                   discardLater)

-------------------------------------------------------------------------------
-- * Observations about Terms

-- | Observations about pairs of terms.
data Observation where
  Equiv   :: (Typeable s1, Typeable s2) => LR -> Term s1 -> Term s2 -> Observation
  Refines :: (Typeable s1, Typeable s2) => LR -> Term s1 -> Term s2 -> Observation
  Implied :: String -> Observation -> Observation

instance Eq Observation where
  (Equiv   lr1 l1 l2) == (Equiv   lr2 r1 r2) = lr1 == lr2 && l1 `eq` r1 && l2 `eq` r2
  (Refines lr1 l1 l2) == (Refines lr2 r1 r2) = lr1 == lr2 && l1 `eq` r1 && l2 `eq` r2
  (Implied s1 o1) == (Implied s2 o2) = s1 == s2 && o1 == o2
  _ == _ = False

-- | Which signature the expressions in an 'Observation' were
-- generated from
data LR
  = LL
  -- ^ Both from the left signature.
  | RR
  -- ^ Both from the right signature.
  | LR
  -- ^ Left from the left signature, right from the right signature.
  | RL
  -- ^ Left from the right signature, right from the left signature.
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-------------------------------------------------------------------------------
-- ** Discovery

-- | Find observations and either annotate a schema or throw it away.
findObservations :: (Foldable f1, Foldable f2, Foldable f3, Eq x, Ord o, Typeable s1, Typeable s2)
  => [(String, x -> Bool)]
  -- ^ Predicates on the seed value. Used to discover observations which only hold with certain
  -- seeds.
  -> (TypeRep -> Char)
  -- ^ Get a variable name from a type.
  -> (schema1 -> schema2 -> Bool)
  -- ^ Some predicate on schemas: if the right schema refines the left schema, normally the left is
  -- marked as \"not the smallest\" UNLESS this predicate holds.
  -> f1 (f2 (schema1, (Maybe (Ann s1 o x), Ann s1 o x)))
  -- ^ First set of schemas. Observations are made between schemas of the two sets.
  -> f3 (schema2, (Maybe (Ann s2 o x), Ann s2 o x))
  -- ^ Second set of schemas.
  -> (ChurchList (schema2, (Maybe (Ann s2 o x), Ann s2 o x)), ChurchList Observation)
findObservations preconditions varf p smallers = foldl' go (cnil, cnil) where
  go (ckept, cobs) z@(schema_a, a0@(old_ann_a, ann_a))
      | isBackground ann_a = (csnoc ckept z, cobs)
      | isJust (allResults ann_a) = case foldl' (foldl' go') (Just ann_a, cnil) smallers of
        (Just final_ann, obs) -> (csnoc ckept (schema_a, (old_ann_a, final_ann)), cappend cobs obs)
        (Nothing, obs)        -> (ckept, cappend cobs obs)
      | otherwise = (csnoc ckept z, cobs)
    where
      go' acc (schema_b, b0@(_, ann_b))
        | isSmallest ann_b && not (isBackground ann_b) =
            let
              go'' (final_ann, obs) (_, refines_ba, ob) =
                let
                  -- if B refines A then: if they are different types, annotate A as not the
                  -- smallest, otherwise throw A away.
                  final_ann'
                    | isNothing final_ann = final_ann
                    | refines_ba && p schema_b schema_a = Nothing
                    | refines_ba = Just (ann_a { isSmallest = False })
                    | otherwise = final_ann
                in (final_ann', maybe id (flip csnoc) ob obs)
            in foldl' go'' acc (allObservations preconditions varf a0 b0)
        | otherwise = acc

-- | Helper for 'observations': all interestingly-distinct observations for a pair of schemas.
allObservations :: (Eq x, Ord o, Typeable s1, Typeable s2)
  => [(String, x -> Bool)]
  -> (TypeRep -> Char)
  -> (Maybe (Ann s1 o x), Ann s1 o x)
  -> (Maybe (Ann s2 o x), Ann s2 o x)
  -> [(Bool, Bool, Maybe Observation)]
allObservations preconditions varf (old_ann_a, ann_a) (old_ann_b, ann_b) =
  (makeConditionalObservations . keepWeakestPreconditions)
  [ (name, obss)
  | precondition  <- Nothing : map Just preconditions
  , let name = fst <$> precondition
  , let prop = maybe (const True) snd precondition
  , let obss = discardLater equalAndIsInstanceOf $ concat
         [ map fst $ discardLater equalAndHasMoreGeneralNaming
           [ (makeObservation prop a b r_a r_b old_ann_a ann_a old_ann_b ann_b, proj)
           | proj <- projections (fst a) (fst b)
           , let (r_a, r_b) = renaming varf proj
           ]
         | let results x = case allResults x of { Just (Some rs) -> rs; _ -> [] }
         , a <- results ann_a
         , b <- results ann_b
         ]
  ]

-- | Helper for 'allObservations': construct an appropriate 'Observation' given the results of
-- execution.
makeObservation :: (Eq x, Ord o, Typeable s1, Typeable s2)
  => (x -> Bool) -- ^ The predicate on the seed value.
  -> (Term s1, (VarResults o x, VarResults o x)) -- ^ The left expression and results.
  -> (Term s2, (VarResults o x, VarResults o x)) -- ^ The right expression and results.
  -> [(String, String)] -- ^ A projection of the variable names in the left term into a consistent namespace.
  -> [(String, String)] -- ^ A projection of the variable names in the right term into a consistent namespace.
  -> Maybe (Ann s1 o x) -- ^ The old left annotation.
  -> Ann s1 o x -- ^ The current left annotation.
  -> Maybe (Ann s2 o x) -- ^ The old right annotation.
  -> Ann s2 o x -- ^ The current right annotation.
  -> (Bool, Bool, Maybe Observation)
makeObservation p (term_a, results_a) (term_b, results_b) renaming_a renaming_b old_ann_a ann_a old_ann_b ann_b =
    (refines_ab, refines_ba, obs)
  where
    -- a failure is uninteresting if the failing term is built out of failing components
    uninteresting_failure =
      (maybe False isFailing old_ann_a && isFailing ann_a) ||
      (maybe False isFailing old_ann_b && isFailing ann_b)

    -- P ⊑ Q iff the results of P are a subset of the results of Q
    (refines_ab, refines_ba) = refines p results_a renaming_a results_b renaming_b

    -- describe the observation
    term_a' = rename renaming_a term_a
    term_b' = rename renaming_b term_b
    obs
      | uninteresting_failure = Nothing
      | refines_ab && refines_ba = Just $
        if exprSize term_a > exprSize term_b then Equiv RL term_b' term_a' else Equiv LR term_a' term_b'
      | refines_ab = Just (Refines LR term_a' term_b')
      | refines_ba = Just (Refines RL term_b' term_a')
      | otherwise = Nothing


-------------------------------------------------------------------------------
-- ** Reasoning

-- | Given two equal observations, check if the second is an instance of the first.  This does not
-- consider 'Implied' observations, as they do not exist at this level.
equalAndIsInstanceOf :: (Eq a, Eq b)
  => (a, b, Maybe Observation)
  -> (a, b, Maybe Observation)
  -> Bool
equalAndIsInstanceOf _ _ = False

-- | Given two equal observations, check if the first has a more general naming than the right.
equalAndHasMoreGeneralNaming :: Eq a => (a, Projection) -> (a, Projection) -> Bool
equalAndHasMoreGeneralNaming _ _ = False

-- | Given a list of (precondition name, observations) values, keep only the weakest preconditions
-- for each observation.
keepWeakestPreconditions :: Eq a => [(p, [a])] -> [(p, [a])]
keepWeakestPreconditions = filter (not . null . snd) . go . sortOn (length . snd) where
  go (p@(_,as):ps) = p : go (map (second (restrict as)) ps)
  go [] = []

  -- if as0 is a subset of as, remove all of as0 from as; otherwise the predicates are unrelated, so
  -- leave the list unmangled.
  restrict as0 as
    | all (`elem` as) as0 = filter (`notElem` as0) as
    | otherwise = as

-- | Given a list of (precondition name, observations) values, turn this into a list of observations
-- conditional on the predicates.
makeConditionalObservations :: [(Maybe String, [(a, b, Maybe Observation)])] -> [(a, b, Maybe Observation)]
makeConditionalObservations = concatMap go where
  go (Just n,  obss) = map (\(ab,ba,mo) -> (ab, ba, Implied n <$> mo)) obss
  go (Nothing, obss) = obss
