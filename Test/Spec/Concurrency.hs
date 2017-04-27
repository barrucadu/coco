{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Test.Spec.Concurrency
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : MonoLocalBinds, ScopedTypeVariables, TupleSections
--
-- Discover observational equalities and refinements between
-- concurrent functions.
--
-- @
-- > :set -XScopedTypeVariables
-- > :{
-- let exprs :: forall t. Exprs (MVar (ConcST t) Int) (ConcST t) Int Int
--     exprs = Exprs { initialState = newMVar
--                   , expressions = [ constant "putMVar_int"  (putMVar  :: MVar (ConcST t) Int -> Int -> ConcST t ())
--                                   , constant "takeMVar_int" (takeMVar :: MVar (ConcST t) Int -> ConcST t Int)
--                                   , constant "readMVar_int" (readMVar :: MVar (ConcST t) Int -> ConcST t Int)
--                                   , constant "succ_int"     (succ     :: Int -> Int)
--                                   , variable "x"            (Proxy    :: Proxy Int)
--                                   ]
--                   , observation = constant "readMVar_int" (readMVar :: MVar (ConcST t) Int -> ConcST t Int)
--                   , eval = evaluate
--                   }
-- :}
-- > mapM_ print $ runST $ discover exprs exprs 5 10
-- takeMVar_int :state: >>= \_ -> takeMVar_int :state:     is equivalent to        takeMVar_int :state:
-- takeMVar_int :state: >>= \_ -> readMVar_int :state:     is equivalent to        takeMVar_int :state:
-- readMVar_int :state: >>= \_ -> takeMVar_int :state:     is equivalent to        takeMVar_int :state:
-- readMVar_int :state: >>= \_ -> readMVar_int :state:     is equivalent to        readMVar_int :state:
-- @
module Test.Spec.Concurrency
  ( -- * Property discovery
    Exprs(..)
  , Observation(..)
  , discover
  , discoverSingle
  , defaultEvaluate
  , defaultTypeInfos
  -- * Building blocks
  , (|||)
  -- * Utilities
  , prettyPrint
  ) where

import Control.Arrow ((***), first, second)
import qualified Control.Concurrent.Classy as C
import Control.DeepSeq (NFData, rnf)
import Control.Monad (void, when)
import Control.Monad.ST (ST)
import Data.Function (on)
import Data.Foldable (toList)
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as L
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, mapMaybe, maybeToList)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Typeable as T
import Data.Void (Void)
import Test.DejaFu (Failure, defaultMemType, defaultWay)
import Test.DejaFu.Common (ThreadAction(..))
import Test.DejaFu.Conc (ConcST, subconcurrency)
import Test.DejaFu.SCT (runSCT')

import Test.Spec.Ann
import Test.Spec.Expr (Schema, Term, allTerms, bind, findInstance, lit, evaluate, exprTypeRep, environment, pp, unBind)
import Test.Spec.Gen (Generator, newGenerator', stepGenerator, getTier, adjustTier)
import Test.Spec.Type (Dynamic, HasTypeRep, coerceDyn, coerceTypeRep, rawTypeRep, unsafeFromDyn)
import Test.Spec.TypeInfo (TypeInfo(..), defaultTypeInfos, getTypeValues, getVariableBaseName)
import Test.Spec.Util

import Test.Spec.Logic

-- | Evaluate an expression, if it has no free variables and it is the
-- correct type.
--
-- If the outer 'Maybe' is @Nothing@, there are free variables. If the
-- inner 'Maybe' is @Nothing@, the type is incorrect.
defaultEvaluate :: (Monad m, HasTypeRep s m a) => Term s m -> [(String, Dynamic s m)] -> Maybe (s -> Maybe a)
defaultEvaluate = evaluate

-------------------------------------------------------------------------------
-- Property discovery

-- | A collection of expressions.
data Exprs s m x = Exprs
  { initialState :: x -> m s
  -- ^ Create a new instance of the state variable.
  , expressions :: [Schema s m]
  -- ^ The primitive expressions to use.
  , backgroundExpressions :: [Schema s m]
  -- ^ Expressions to use as helpers for building new
  -- expressions. Observations will not be reported about terms which
  -- are entirely composed of background expressions.
  , observation :: s -> m x
  -- ^ The observation to make.
  , eval :: Term s m -> [(String, Dynamic s m)] -> Maybe (s -> Maybe (m ()))
  -- ^ Evaluate an expression. In practice this will just be
  -- 'defaultEvaluate', but it's here to make the types work out.
  , setState :: s -> x -> m ()
  -- ^ Set the state value. This doesn't need to be atomic, or even
  -- guaranteed to work, its purpose is to cause interference when
  -- evaluating other terms.
  }

-- | Attempt to discover properties of the given set of concurrent
-- operations. Returns three sets of observations about, respectively:
-- the first set of expressions; the second set of expressions; and
-- the combination of the two.
discover :: forall s1 s2 t x. (Ord x, T.Typeable x, NFData x)
  => [(T.TypeRep, TypeInfo)]
  -- ^ Information about types. There MUST be an entry for every hole and seed type!
  -> [(String, x -> Bool)]
  -- ^ Predicates on the seed value. Used to discover properties which
  -- only hold with certain seeds.
  -> Exprs s1 (ConcST t) x
  -- ^ A collection of expressions
  -> Exprs s2 (ConcST t) x
  -- ^ Another collection of expressions.
  -> Int
  -- ^ Term size limit
  -> ST t ([Observation], [Observation], [Observation])
discover typeInfos seedPreds exprs1 exprs2 =
  case lookup (T.typeRep (Proxy :: Proxy x)) typeInfos of
    Just tyI ->
      let seeds = mapMaybe unsafeFromDyn (listValues tyI)
      in discoverWithSeeds typeInfos seedPreds exprs1 exprs2 seeds
    Nothing  -> \_ -> pure ([], [], [])

-- | Like 'discover', but takes a list of seeds.
discoverWithSeeds :: (Ord x, NFData x)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Exprs s1 (ConcST t) x
  -> Exprs s2 (ConcST t) x
  -> [x]
  -> Int
  -> ST t ([Observation], [Observation], [Observation])
discoverWithSeeds typeInfos seedPreds exprs1 exprs2 seeds lim = do
    (g1, obs1) <- discoverSingleWithSeeds' typeInfos seedPreds exprs1 seeds lim
    (g2, obs2) <- discoverSingleWithSeeds' typeInfos seedPreds exprs2 seeds lim
    let obs3 = crun (findObservations g1 g2 0)
    pure (obs1, obs2, obs3)
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
discoverSingle :: forall s t x. (Ord x, T.Typeable x, NFData x)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Exprs s (ConcST t) x
  -> Int
  -> ST t [Observation]
discoverSingle typeInfos seedPreds exprs =
  case lookup (T.typeRep (Proxy :: Proxy x)) typeInfos of
    Just tyI ->
      let seeds = mapMaybe unsafeFromDyn (listValues tyI)
      in discoverSingleWithSeeds typeInfos seedPreds exprs seeds
    Nothing  -> \_ -> pure []

-- | Like 'discoverSingle', but takes a list of seeds.
discoverSingleWithSeeds :: (Ord x, NFData x)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Exprs s (ConcST t) x
  -> [x]
  -> Int
  -> ST t [Observation]
discoverSingleWithSeeds typeInfos seedPreds exprs seeds lim =
  snd <$> discoverSingleWithSeeds' typeInfos seedPreds exprs seeds lim

-- | Like 'discoverSingleWithSeeds', but returns the generator.
discoverSingleWithSeeds' :: forall s t x. (Ord x, NFData x)
  => [(T.TypeRep, TypeInfo)]
  -> [(String, x -> Bool)]
  -> Exprs s (ConcST t) x
  -> [x]
  -> Int
  -> ST t (Generator s (ConcST t) (Maybe (Ann s (ConcST t) x), Ann s (ConcST t) x), [Observation])
discoverSingleWithSeeds' typeInfos seedPreds exprs seeds lim =
    let g = newGenerator'([(e, (Nothing, initialAnn False)) | e <- expressions           exprs] ++
                          [(e, (Nothing, initialAnn True))  | e <- backgroundExpressions exprs])
    in second crun <$> findObservations g 0
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g tier = do
      evaled <- mapM evalSchema . S.toList $ getTier tier g
      let smallers = map (`getTier` g) [0..tier-1]
      let (kept, observations) = first crun (observe seedPreds varfun ((==) `on` exprTypeRep) smallers evaled)
      let g' = adjustTier (const (S.fromList kept)) tier g
      second (cappend observations) <$> if tier == lim
        then pure (g', cnil)
        else findObservations (stepGenerator checkNewTerm g') (tier+1)

    -- evaluate all terms of a schema and store their results
    evalSchema (schema, (_, ann)) = case allTerms varfun schema of
      (mostGeneralTerm:rest) -> do
        mresult <- evalTerm mostGeneralTerm
        let new_ann = case mresult of
              Just (atomic, no_interference, interference) ->
                let getResults = getResultsFrom mostGeneralTerm
                    resultsOf t = (\r1 r2 -> (t, (r1, r2))) <$> getResults no_interference t <*> getResults interference t
                    results      = mapMaybe resultsOf rest
                    all_results  = (mostGeneralTerm, (no_interference, interference)) : results
                in update atomic (Some all_results) ann
              Nothing -> update False None ann
        pure (schema, (Just ann, new_ann))
      [] -> pure (schema, (Just ann, update False None ann))

    -- evaluate a term
    evalTerm term = do
      maybe_no_interference <- run False term
      maybe_interference    <- run True  term
      pure $ do
        (atomic, no_interference) <- maybe_no_interference
        (_,      interference)    <- maybe_interference
        pure (atomic, no_interference, interference)

    -- evaluate a term with optional interference
    run :: Bool -> Term s (ConcST t) -> ST t (Maybe (Bool, NonEmpty (VarAssignment x, Set (Maybe Failure, x))))
    run interference term = shoveMaybe (runSingle typeInfos exprs interference term seeds)

    -- get the base name for a variable
    varfun = getVariableBaseName typeInfos

-- | Get the results of a more specific term from a more general one
getResultsFrom :: Foldable f
  => Term s m -- ^ The general term.
  -> f (VarAssignment x, Set (Maybe Failure, x)) -- ^ Its results.
  -> Term s m -- ^ The specific term.
  -> Maybe (NonEmpty (VarAssignment x, Set (Maybe Failure, x)))
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
-- Building blocks

-- | Concurrent composition. Waits for both component computations to
-- finish.
(|||) :: ConcST t a -> ConcST t b -> ConcST t ()
a ||| b = do
  j <- C.spawn a
  void b
  void (C.readMVar j)


-------------------------------------------------------------------------------
-- Misc

-- | Pretty-print a list of observations.
prettyPrint :: [(T.TypeRep, TypeInfo)] -> [Observation] -> IO ()
prettyPrint typeInfos obss0 = mapM_ (putStrLn . pad) (sortOn cmp obss) where
  obss = map go obss0 where
    go (Equiv   e1 e2) = (Nothing, pp nf e1, "===", pp nf e2)
    go (Refines e1 e2) = (Nothing, pp nf e1, "=[=", pp nf e2)
    go (Implied p obs) = let (Nothing, e1, t, e2) = go obs in (Just p, e1, t, e2)

  cmp (p, e1, _, e2) = (maybe 0 length p, p, length e1, e1, length e2, e2)

  pad (p, e1, t, e2) =
    let off = replicate (maxlen p - length e1) ' '
        prefix = maybe "" (++ "  ==>  ") p
    in prefix ++ off ++ e1 ++ "  " ++ t ++ "  " ++ e2

  maxlen p0 = maximum (map (\(p, e1, _, _) -> if p == p0 then length e1 else 0) obss)

  nf = getVariableBaseName typeInfos


-------------------------------------------------------------------------------
-- Utilities

-- | Run a concurrent program many times, gathering the results. Up to
-- 'numVariants' values of every free variable, including the seed,
-- are tried in all combinations.
runSingle :: forall s t x. (Ord x, NFData x)
  => [(T.TypeRep, TypeInfo)]
  -> Exprs s (ConcST t) x
  -> Bool
  -> Term s (ConcST t)
  -> [x]
  -> Maybe (ST t (Bool, NonEmpty (VarAssignment x, Set (Maybe Failure, x))))
runSingle typeInfos exprs interference expr seeds
    | null assignments = Nothing
    | otherwise = Just $ do
        out <- (and *** L.fromList) . unzip <$> mapM go assignments
        rnf out `seq` pure out
  where
    go (varassign, eval_expr) = do
      rs <- runSCT' defaultWay defaultMemType $ do
        s <- initialState exprs (seedVal varassign)
        r <- subconcurrency $ do
          when interference $
            void . C.fork . setState exprs s $ seedVal varassign
          shoveMaybe (eval_expr s)
        x <- observation exprs s
        pure (either Just (const Nothing) r, x)
      -- very rough interpretation of atomicity: the trace has one
      -- thing in it other than the stop!
      let is_atomic trc =
            let relevant = filter (\(_,_,ta) -> ta /= Return) .
                           takeWhile (\(_,_,ta) -> ta /= StopSubconcurrency && ta /= Stop) .
                           drop 1 .
                           dropWhile (\(_,_,ta) -> ta /= Subconcurrency)
            in length (relevant trc) == 1
      let out = (all (is_atomic . snd) rs, (varassign, smapMaybe eitherToMaybe . S.fromList $ map fst rs))
      -- strictify, to avoid wasting memory on intermediate results.
      rnf out `seq` pure out

    assignments =
      [ (VA seed (M.fromList vidmap), eval_expr)
      | seed <- take numVariants seeds
      , (vidmap, eval_expr) <- assign [] vars expr
      ]

    assign env ((var, dyns):free) e =
      [ ((var, vid):vidlist, eval_expr)
      | (vid, Just dyn) <- map (second coerceDyn) . take numVariants $ zip [0..] dyns
      , (vidlist, eval_expr) <- assign ((var, dyn):env) free e
      ]
    assign env [] e = maybeToList $ (\r -> ([], r)) <$> (evoid e >>= \e' -> eval exprs e' env)

    vars :: [(String, [Dynamic Void Void1])]
    vars = ordNubOn fst (map (second enumerateValues) (freeVars expr))
    freeVars = mapMaybe (\(var, ty) -> (,) <$> pure var <*> coerceTypeRep ty) . environment

    evoid e = bind [] e (lit "" (pure () :: ConcST t ()))

    enumerateValues = getTypeValues typeInfos . rawTypeRep

-- | Filter for term generation: only generate out of non-boring
-- terms; and only generate binds out of smallest terms.
checkNewTerm :: (a, Ann s m x) -> (a, Ann s m x) -> Schema s m -> Bool
checkNewTerm (_, ann1) (_, ann2) expr
  | isBoring ann1 || isBoring ann2 = False
  | otherwise = case unBind expr of
      Just ([], _, _) -> isSmallest ann1 && isSmallest ann2
      Just _ -> isSmallest ann2
      _ -> True

-- | Number of variants of a value to consider.
numVariants :: Int
numVariants = 10
