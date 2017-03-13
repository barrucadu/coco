{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Test.Spec.Concurrency
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs, ScopedTypeVariables, TupleSections
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
  , defaultListValues
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
import Data.List (foldl', sortOn)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as L
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe, maybeToList)
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
import Test.Spec.Expr (Expr, bind, constant, dynConstant, evaluate, exprSize, exprTypeRep, freeVariables, let_, rename, unBind)
import Test.Spec.Gen (Generator, newGenerator', stepGenerator, getTier', adjustTier)
import Test.Spec.List (defaultListValues)
import Test.Spec.Type (Dynamic, HasTypeRep, TypeRep, coerceDyn, coerceTypeRep, unsafeFromDyn, unsafeFromRawTypeRep)
import Test.Spec.Util

-- | Evaluate an expression, if it has no free variables and it is the
-- correct type.
--
-- If the outer 'Maybe' is @Nothing@, there are free variables. If the
-- inner 'Maybe' is @Nothing@, the type is incorrect.
defaultEvaluate :: (Monad m, HasTypeRep s m a) => Expr s m -> Maybe (s -> Maybe a)
defaultEvaluate = evaluate

-------------------------------------------------------------------------------
-- Property discovery

data Observation where
  Equiv   :: Expr s1 m -> Expr s2 m -> Observation
  Refines :: Expr s1 m -> Expr s2 m -> Observation

instance Eq Observation where
  (Equiv   l1 l2) == (Equiv   r1 r2) = show (rename l1) == show (rename r1) && show (rename l2) == show (rename r2)
  (Refines l1 l2) == (Refines r1 r2) = show (rename l1) == show (rename r1) && show (rename l2) == show (rename r2)
  _ == _ = False

instance Show Observation where
  show (Equiv   a b) = show a ++ "\tis equivalent to\t" ++ show b
  show (Refines a b) = show a ++ "\tstrictly refines\t" ++ show b

-- | A collection of expressions.
data Exprs s m x = Exprs
  { initialState :: x -> m s
  -- ^ Create a new instance of the state variable.
  , expressions :: [Expr s m]
  -- ^ The primitive expressions to use.
  , backgroundExpressions :: [Expr s m]
  -- ^ Expressions to use as helpers for building new
  -- expressions. Observations will not be reported about terms which
  -- are entirely composed of background expressions.
  , observation :: s -> m x
  -- ^ The observation to make.
  , eval :: Expr s m -> Maybe (s -> Maybe (m ()))
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
discover :: forall x s1 s2 t. (Ord x, T.Typeable x, NFData x)
         => (TypeRep Void Void1 -> [Dynamic Void Void1]) -- ^ List values of the demanded type.
         -> Exprs s1 (ConcST t) x -- ^ A collection of expressions
         -> Exprs s2 (ConcST t) x -- ^ Another collection of expressions.
         -> Int -- ^ Term size limit
         -> ST t ([Observation], [Observation], [Observation])
discover listValues exprs1 exprs2 =
  let seedty = unsafeFromRawTypeRep $ T.typeRep (Proxy :: Proxy x)
      seeds  = mapMaybe unsafeFromDyn $ listValues seedty
  in discoverWithSeeds listValues exprs1 exprs2 seeds

-- | Like 'discover', but takes a list of seeds.
discoverWithSeeds :: (Ord x, NFData x)
                  => (TypeRep Void Void1 -> [Dynamic Void Void1])
                  -> Exprs s1 (ConcST t) x
                  -> Exprs s2 (ConcST t) x
                  -> [x]
                  -> Int
                  -> ST t ([Observation], [Observation], [Observation])
discoverWithSeeds listValues exprs1 exprs2 seeds lim = do
    (g1, obs1) <- discoverSingleWithSeeds' listValues exprs1 seeds lim
    (g2, obs2) <- discoverSingleWithSeeds' listValues exprs2 seeds lim
    let obs3 = crun (findObservations g1 g2 0)
    pure (obs1, obs2, obs3)
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g1 g2 = go where
      go tier =
        let exprs = getTier' tier g1
            smallers = map (`getTier'` g2) [0..tier]
            observations = foldl' (check smallers) cnil exprs
        in cappend observations $ if tier == lim then cnil else go (tier+1)

    check smallers cobs ((old_ann_a, ann_a), expr_a)
        | isBackground ann_a = cobs
        | isJust (allResults ann_a) = cappend cobs (foldl' (foldl' go) cnil smallers)
        | otherwise = cobs
      where
        go obs ((old_ann_b, ann_b), expr_b)
          | isBackground ann_b = obs
          | otherwise =
            let (_, _, ob) = mkobservation expr_a expr_b old_ann_a ann_a old_ann_b ann_b
            in maybe id (flip csnoc) ob obs


-- | Like 'discover', but only takes a single set of expressions. This
-- will lead to better pruning.
discoverSingle :: forall x s t. (Ord x, T.Typeable x, NFData x)
               => (TypeRep Void Void1 -> [Dynamic Void Void1])
               -> Exprs s (ConcST t) x
               -> Int
               -> ST t [Observation]
discoverSingle listValues exprs =
  let seedty = unsafeFromRawTypeRep $ T.typeRep (Proxy :: Proxy x)
      seeds  = mapMaybe unsafeFromDyn $ listValues seedty
  in discoverSingleWithSeeds listValues exprs seeds

-- | Like 'discoverSingle', but takes a list of seeds.
discoverSingleWithSeeds :: (Ord x, NFData x)
                        => (TypeRep Void Void1 -> [Dynamic Void Void1])
                        -> Exprs s (ConcST t) x
                        -> [x]
                        -> Int
                        -> ST t [Observation]
discoverSingleWithSeeds listValues exprs seeds lim =
  snd <$> discoverSingleWithSeeds' listValues exprs seeds lim

-- | Like 'discoverSingleWithSeeds', but returns the generator.
discoverSingleWithSeeds' :: forall s t x. (Ord x, NFData x)
                         => (TypeRep Void Void1 -> [Dynamic Void Void1])
                         -> Exprs s (ConcST t) x
                         -> [x]
                         -> Int
                         -> ST t (Generator s (ConcST t) (Maybe (Ann x), Ann x), [Observation])
discoverSingleWithSeeds' listValues exprs seeds lim =
    let g = newGenerator'([((Nothing, initialAnn False), e) | e <- expressions           exprs] ++
                          [((Nothing, initialAnn True),  e) | e <- backgroundExpressions exprs])
    in second crun <$> findObservations g 0
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g tier = do
      evaled <- mapM evalTerm (getTier' tier g)
      let smallers = map (`getTier'` g) [0..tier-1]
      let (kept, observations) = first crun (foldl' (check smallers) (cnil, cnil) evaled)
      let g' = adjustTier (const kept) tier g
      second (cappend observations) <$> if tier == lim
        then pure (g', cnil)
        else findObservations (stepGenerator checkNewTerm g') (tier+1)

    -- evaluate a term and store its results
    evalTerm ((_, ann), expr) = do
      maybe_no_interference <- run False expr
      maybe_interference    <- run True  expr
      let atomic          = maybe False fst maybe_no_interference
      let no_interference = snd <$> maybe_no_interference
      let interference    = snd <$> maybe_interference
      pure ((Just ann, update atomic no_interference interference ann), expr)

    -- find observations and either annotate a term or throw it away.
    check smallers (ckept, cobs) a@((old_ann_a, ann_a), expr_a)
        | isBackground ann_a = (csnoc ckept a, cobs)
        | isJust (allResults ann_a) = case foldl' (foldl' go) (Just ann_a, cnil) smallers of
          (Just final_ann, obs) -> (csnoc ckept ((old_ann_a, final_ann), expr_a), cappend cobs obs)
          (Nothing, obs)        -> (ckept, cappend cobs obs)
        | otherwise = (csnoc ckept a, cobs)
      where
        go acc@(final_ann, obs) ((old_ann_b, ann_b), expr_b)
          | isSmallest ann_b && not (isBackground ann_b) =
              let (_, refines_ba, ob) = mkobservation expr_a expr_b old_ann_a ann_a old_ann_b ann_b
                  -- if B refines A then: if they are different types,
                  -- annotate A as not the smallest, otherwise throw A
                  -- away.
                  final_ann'
                    | isNothing final_ann = final_ann
                    | refines_ba && exprTypeRep expr_a == exprTypeRep expr_b = Nothing
                    | refines_ba = Just (ann_a { isSmallest = False })
                    | otherwise = final_ann
              in (final_ann', maybe id (flip csnoc) ob obs)
          | otherwise = acc

    -- evaluate a expression.
    run :: Bool -> Expr s (ConcST t) -> ST t (Maybe (Bool, NonEmpty (VarAssignment x, Set (Maybe Failure, x))))
    run interference expr = shoveMaybe (runSingle listValues exprs interference expr seeds)


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
prettyPrint :: [Observation] -> IO ()
prettyPrint obss0 = mapM_ (putStrLn . pad) (sortOn cmp obss) where
  obss = map go obss0 where
    go (Equiv   e1 e2) = (show e1, "is equivalent to", show e2)
    go (Refines e1 e2) = (show e1, "strictly refines", show e2)

  cmp (e1, _, e2) = (length e1, e1, length e2, e2)

  pad (e1, t, e2) =
    replicate (maxlen - length e1) ' ' ++ e1 ++ "        " ++ t ++ "        " ++ e2

  maxlen = maximum (map (\(e1, _, _) -> length e1) obss)

-------------------------------------------------------------------------------
-- Utilities

-- | Run a concurrent program many times, gathering the results. Up to
-- 'numVariants' values of every free variable, including the seed,
-- are tried in all combinations.
runSingle :: forall s t x. (Ord x, NFData x)
          => (TypeRep Void Void1 -> [Dynamic Void Void1])
          -> Exprs s (ConcST t) x
          -> Bool
          -> Expr s (ConcST t)
          -> [x]
          -> Maybe (ST t (Bool, NonEmpty (VarAssignment x, Set (Maybe Failure, x))))
runSingle listValues exprs interference expr seeds
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
      , (vidmap, eval_expr) <- assign vars expr
      ]

    assign ((var, dyns):vs) e =
      [ ((var, vid):vidlist, eval_expr)
      | (vid, dyn) <- take numVariants $ zip [0..] dyns
      , Just e' <- [(\d -> let_ var (dynConstant "@" d) e) =<< coerceDyn dyn]
      , (vidlist, eval_expr) <- assign vs e'
      ]
    assign [] e = maybeToList $ (\r -> ([], r)) <$> (eval exprs =<< evoid e)

    vars = ordNubOn fst (map (second listValues) (freeVars expr))
    freeVars = mapMaybe (\(var, ty) -> (,) <$> pure var <*> coerceTypeRep ty) . freeVariables

    evoid e = bind "_" e (constant "" (pure () :: ConcST t ()))

-- | Helper for 'discover' and 'discoverSingle': construct an
-- appropriate 'Observation' given the results of execution.
mkobservation :: Ord x
              => Expr s1 m -- ^ The left expression.
              -> Expr s2 m -- ^ The right expression.
              -> Maybe (Ann x) -- ^ The old left annotation.
              -> Ann x -- ^ The current left annotation.
              -> Maybe (Ann x) -- ^ The old right annotation.
              -> Ann x -- ^ The current right annotation.
              -> (Bool, Bool, Maybe Observation)
mkobservation expr_a expr_b old_ann_a ann_a old_ann_b ann_b = (refines_ab, refines_ba, obs) where
  -- a failure is uninteresting if the failing term is built out of failing components
  uninteresting_failure =
    (maybe False isFailing old_ann_a && isFailing ann_a) ||
    (maybe False isFailing old_ann_b && isFailing ann_b)

  -- P ⊑ Q iff the results of P are a subset of the results of Q
  (refines_ab, refines_ba) = fromMaybe (False, False) (refines ann_a ann_b)

  -- describe the observation
  obs
    | uninteresting_failure = Nothing
    | refines_ab && refines_ba = Just $
      if exprSize expr_a > exprSize expr_b then Equiv expr_b expr_a else Equiv expr_a expr_b
    | refines_ab = Just (Refines expr_a expr_b)
    | refines_ba = Just (Refines expr_b expr_a)
    | otherwise = Nothing

-- | Filter for term generation: only generate out of non-boring
-- terms; and only generate binds out of smallest terms.
checkNewTerm :: (a, Ann x) -> (b, Ann x) -> Expr s m -> Bool
checkNewTerm (_, ann1) (_, ann2) expr
  | isBoring ann1 || isBoring ann2 = False
  | otherwise = case unBind expr of
      Just ("_", _, _) -> isSmallest ann1 && isSmallest ann2
      Just _ -> isSmallest ann2
      _ -> True

-- | Number of variants of a value to consider.
numVariants :: Int
numVariants = 10
