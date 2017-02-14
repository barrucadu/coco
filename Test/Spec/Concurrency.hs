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
  ) where

import Control.Arrow (second)
import qualified Control.Concurrent.Classy as C
import Control.Monad (join)
import Control.Monad.ST (ST)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as L
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe, maybeToList)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Typeable as T
import Data.Void (Void)
import Test.DejaFu (Failure, defaultBounds, defaultMemType)
import Test.DejaFu.Conc (ConcST, subconcurrency)
import Test.DejaFu.SCT (sctBound)

import Test.Spec.Ann
import Test.Spec.Expr (Expr, ($$), bind, constant, dynConstant, evaluate, exprSize, exprTypeRep, freeVariables, let_, rename, stateVariable, tyVariable, variable, unBind)
import Test.Spec.Gen (Generator, newGenerator', stepGenerator, filterTier, getTier)
import Test.Spec.List (defaultListValues)
import Test.Spec.Type (Dynamic, HasTypeRep, TypeRep, coerceDyn, coerceTypeRep, monadTyCon, unsafeFromDyn, unsafeFromRawTypeRep, unsafeToDyn)
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
  show (Refines a b) = show a ++ "\trefines\t"          ++ show b

-- | A collection of expressions.
data Exprs s m x a = Exprs
  { initialState :: a -> m s
  -- ^ Create a new instance of the state variable.
  , expressions :: [Expr s m]
  -- ^ The primitive expressions to use.
  , observation :: Expr s m
  -- ^ The observation to make. This should be a function of type
  -- @s -> m x@. If it's not, you will get bogus results.
  , eval :: Expr s m -> Maybe (s -> Maybe (m (Maybe Failure, x)))
  -- ^ Evaluate an expression. In practice this will just be
  -- 'defaultEvaluate', but it's here to make the types work out.
  }

-- | Attempt to discover properties of the given set of concurrent
-- operations. Returns three sets of observations about, respectively:
-- the first set of expressions; the second set of expressions; and
-- the combination of the two.
discover :: forall x a s1 s2 t. (Ord x, T.Typeable a, T.Typeable x)
         => (TypeRep Void Void1 -> [Dynamic Void Void1]) -- ^ List values of the demanded type.
         -> Exprs s1 (ConcST t) x a -- ^ A collection of expressions
         -> Exprs s2 (ConcST t) x a -- ^ Another collection of expressions.
         -> Int -- ^ Term size limit
         -> ST t ([Observation], [Observation], [Observation])
discover listValues exprs1 exprs2 =
  let seedty = unsafeFromRawTypeRep $ T.typeRep (Proxy :: Proxy a)
      seeds  = mapMaybe unsafeFromDyn $ listValues seedty
  in discoverWithSeeds listValues exprs1 exprs2 seeds

-- | Like 'discover', but takes a list of seeds.
discoverWithSeeds :: (Ord x, T.Typeable x)
                  => (TypeRep Void Void1 -> [Dynamic Void Void1])
                  -> Exprs s1 (ConcST t) x a
                  -> Exprs s2 (ConcST t) x a
                  -> [a]
                  -> Int
                  -> ST t ([Observation], [Observation], [Observation])
discoverWithSeeds listValues exprs1 exprs2 seeds lim = do
    (g1, obs1) <- discoverSingleWithSeeds' listValues exprs1 seeds lim
    (g2, obs2) <- discoverSingleWithSeeds' listValues exprs2 seeds lim
    let obs3 = concat (findObservations g1 g2 0)
    pure (obs1, obs2, obs3)
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g1 g2 = go where
      go tier = do
        let observations = mapMaybe (check g1 g2) (pairs True tier g1 g2)
        (observations:) $ if tier == lim
          then []
          else go (tier+1)

    -- check if a pair of terms are observationally equal, or if one
    -- is a refinement of the other.
    check g1 g2 ((ann_a, expr_a), (ann_b, expr_b)) = case (,) <$> allResults ann_a <*> allResults ann_b of
      Just _  -> snd $ mkobservation False g1 g2 expr_a expr_b Nothing ann_a Nothing ann_b
      Nothing -> Nothing

-- | Like 'discover', but only takes a single set of expressions. This
-- will lead to better pruning.
discoverSingle :: forall x a s t. (Ord x, T.Typeable a, T.Typeable x)
               => (TypeRep Void Void1 -> [Dynamic Void Void1])
               -> Exprs s (ConcST t) x a
               -> Int
               -> ST t [Observation]
discoverSingle listValues exprs =
  let seedty = unsafeFromRawTypeRep $ T.typeRep (Proxy :: Proxy a)
      seeds  = mapMaybe unsafeFromDyn $ listValues seedty
  in discoverSingleWithSeeds listValues exprs seeds

-- | Like 'discoverSingle', but takes a list of seeds.
discoverSingleWithSeeds :: (Ord x, T.Typeable x)
                        => (TypeRep Void Void1 -> [Dynamic Void Void1])
                        -> Exprs s (ConcST t) x a
                        -> [a]
                        -> Int
                        -> ST t [Observation]
discoverSingleWithSeeds listValues exprs seeds lim =
  snd <$> discoverSingleWithSeeds' listValues exprs seeds lim

-- | Like 'discoverSingleWithSeeds', but returns the generator.
discoverSingleWithSeeds' :: forall s t x a. (Ord x, T.Typeable x)
                         => (TypeRep Void Void1 -> [Dynamic Void Void1])
                         -> Exprs s (ConcST t) x a
                         -> [a]
                         -> Int
                         -> ST t (Generator s (ConcST t) (Ann x), [Observation])
discoverSingleWithSeeds' listValues exprs seeds lim =
    let g = newGenerator' [(initialAnn, e) | e <- expressions exprs]
    in second concat <$> findObservations g 0
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations g tier = do
      (g', observations) <- mapAccumLM check g (pairs False tier g g)
      second (catMaybes observations:) <$> if tier == lim
        then pure (g', [])
        else findObservations (stepGenerator checkGenBind g') (tier+1)

    -- check if a pair of terms are observationally equal, or if one
    -- is a refinement of the other.
    check g ((ann_a, expr_a), (ann_b, expr_b)) = do
      ann_a' <- if isJust (allResults ann_a) then pure ann_a else (`update` ann_a) <$> run expr_a
      ann_b' <- if isJust (allResults ann_b) then pure ann_b else (`update` ann_b) <$> run expr_b

      let g' = annotate expr_b ann_b' . annotate expr_a ann_a' $ g

      case (,) <$> allResults ann_a' <*> allResults ann_b' of
        Just _ ->
          let (g'', obs) = mkobservation (exprTypeRep expr_a == exprTypeRep expr_b) g' g' expr_a expr_b (Just ann_a) ann_a' (Just ann_b) ann_b'
          in pure (maybe g' (either id id) g'', obs)
        Nothing -> pure (g', Nothing)

    -- evaluate a expression.
    run :: Expr s (ConcST t) -> ST t (Maybe (NonEmpty (VarAssignment, Set (Maybe Failure, x))))
    run expr = shoveMaybe (runSingle listValues exprs expr seeds)


-------------------------------------------------------------------------------
-- Building blocks

-- | Concurrent composition. Waits for the two component computations
-- to finish.
(|||) :: ConcST t () -> ConcST t () -> ConcST t ()
a ||| b = do
  j1 <- C.spawn a
  j2 <- C.spawn b
  C.takeMVar j1
  C.takeMVar j2


-------------------------------------------------------------------------------
-- Utilities

-- | Run a concurrent program many times, gathering the results. Up to
-- 'numVariants' values of every free variable, including the seed,
-- are tried in all combinations.
runSingle :: forall t s x a. (Ord x, T.Typeable x)
        => (TypeRep Void Void1 -> [Dynamic Void Void1])
        -> Exprs s (ConcST t) x a
        -> Expr s (ConcST t)
        -> [a]
        -> Maybe (ST t (NonEmpty (VarAssignment, Set (Maybe Failure, x))))
runSingle listValues exprs expr seeds
    | null assignments = Nothing
    | otherwise = Just $ L.fromList <$> mapM go assignments
  where
    go (varassign, eval_expr, seed) = do
      rs <- runConc $ shoveMaybe . eval_expr =<< initialState exprs seed
      -- strictify, to avoid wasting memory on intermediate results.
      let rs' = smapMaybe (join . eitherToMaybe) rs
      S.size rs' `seq` pure (varassign, rs')

    assignments =
      [ ((sid, M.fromList vidmap), eval_expr, seed)
      | (sid, seed) <- take numVariants $ zip [0..] seeds
      , (vidmap, eval_expr) <- assign vars expr
      ]

    assign :: [(String, [Dynamic Void Void1])] -> Expr s (ConcST t) -> [([(String, Int)], s -> Maybe (ConcST t (Maybe Failure, x)))]
    assign ((var, dyns):vs) e =
      [ ((var, vid):vidlist, eval_expr)
      | (vid, dyn) <- take numVariants $ zip [0..] dyns
      , Just e' <- [(\d -> let_ var (dynConstant "@" d) e) =<< coerceDyn dyn]
      , (vidlist, eval_expr) <- assign vs e'
      ]
    assign [] e = maybeToList $ (\r -> ([], r)) <$> evalAndObserve e

    vars = ordNubOn fst (map (second listValues) (freeVars expr))
    freeVars = mapMaybe (\(var, ty) -> (,) <$> pure var <*> coerceTypeRep ty) . freeVariables

    evalAndObserve e = eval exprs =<< e `andObserveWith` exprs

-- | Subconcurrently run an expression, and observe the state variable.
andObserveWith :: forall s t x a. T.Typeable x => Expr s (ConcST t) -> Exprs s (ConcST t) x a -> Maybe (Expr s (ConcST t))
andObserveWith expr exprs = do
  let efuty = T.typeRep (Proxy :: Proxy (Either Failure ()))
  let xty   = T.typeRep (Proxy :: Proxy x)
  let mfxty = T.typeRep (Proxy :: Proxy (Maybe Failure, x))
  let outty = T.mkFunTy efuty (T.mkFunTy xty (T.mkTyConApp monadTyCon [mfxty]))

  let esubc = constant   "subconcurrency" (subconcurrency :: ConcST t () -> ConcST t (Either Failure ()))
  let efvar = variable   "fvar" (Proxy :: Proxy (Either Failure ()))
  let eovar = tyVariable "ovar" (unsafeFromRawTypeRep xty)
  let eout  = dynConstant "out" $ unsafeToDyn outty ((\a b -> pure (either Just (const Nothing) a, b)) :: Either a b -> c -> ConcST t (Maybe a, c))
  let evoid = constant   "void" (pure () :: ConcST t ())

  -- out fvar over
  e1 <- (eout $$ efvar) >>= ($$ eovar)
  -- OBS :state:
  e2 <- observation exprs $$ stateVariable
  -- E2 >>= \ovar -> E1
  e3 <- bind "ovar" e2 e1
  -- EXPR >>= \_ -> pure ()
  e4 <- bind "_" expr evoid
  -- subconcurrency E4
  e5 <- esubc $$ e4
  -- E5 >>= \fvar -> E3
  bind "fvar" e5 e3

-- | Run a concurrent computation, producing the set of all results.
runConc :: Ord a => ConcST t a -> ST t (Set (Either Failure a))
runConc c =
  S.fromList . map fst <$> sctBound defaultMemType defaultBounds c

-- | Helper for 'discover' and 'discoverSingle': construct an
-- appropriate 'Observation' given the results of execution. The left
-- and right annotations may have been changed: this is used to
-- determine if a failure is interesting or not.
--
-- TODO: This is pretty messy, combining the annotation changes with
-- the observation. Maybe better to split it up?

-- mkobservation (exprtypeRep expr_a == exprTypeRep expr_b) g' g' expr_a expr_b (Just ann_a) ann_a' (Just ann_b) ann_b'

mkobservation :: Ord x
              => Bool -- ^ Whether the expressions are the same type.
              -> Generator s1 m (Ann x) -- ^ The left generator.
              -> Generator s2 m (Ann x) -- ^ The right generator.
              -> Expr s1 m -- ^ The left expression.
              -> Expr s2 m -- ^ The right expression.
              -> Maybe (Ann x) -- ^ The old left annotation.
              -> Ann x -- ^ The current left annotation.
              -> Maybe (Ann x) -- ^ The old right annotation.
              -> Ann x -- ^ The current right annotation.
              -> (Maybe (Either (Generator s1 m (Ann x)) (Generator s2 m (Ann x))), Maybe Observation)
mkobservation same_type g1 g2 expr_a expr_b old_ann_a ann_a old_ann_b ann_b = (g12', obs) where
  -- a failure is uninteresting if the failing term is built out of failing components
  uninteresting_failure =
    (maybe False isFailing old_ann_a && isFailing ann_a) ||
    (maybe False isFailing old_ann_b && isFailing ann_b)

  -- P ⊑ Q iff the results of P are a subset of the results of Q
  (refines_ab, refines_ba) = fromMaybe (False, False) (refines ann_a ann_b)

  -- if there is a refinement, remove the larger expression from the generator
  g12'
    | refines_ab && (not refines_ba || refines_ba && exprSize expr_b >= exprSize expr_a) =
      Just . Right $ if same_type
                     then filterTier ((/=expr_b) . snd) (exprSize expr_b) g2
                     else annotate expr_b (ann_b { isSmallest = False }) g2
    | refines_ba && (not refines_ab || refines_ab && exprSize expr_a >= exprSize expr_b) =
      Just . Left  $ if same_type
                     then filterTier ((/=expr_a) . snd) (exprSize expr_a) g1
                     else annotate expr_a (ann_a { isSmallest = False }) g1
    | otherwise = Nothing

  -- describe the observation
  obs
    | uninteresting_failure = Nothing
    | refines_ab && refines_ba = Just $
      if exprSize expr_a > exprSize expr_b then Equiv expr_b expr_a else Equiv expr_a expr_b
    | refines_ab = Just (Refines expr_a expr_b)
    | refines_ba = Just (Refines expr_b expr_a)
    | otherwise = Nothing

-- | Helper for 'discover' and 'discoverSingle': find pairs of
-- expressions to try checking for equality and refinement.
pairs :: Bool -- ^ Whether to go up to and including the tier in the right generator.
      -> Int -- ^ The current tier.
      -> Generator s1 m (Ann x1) -- ^ The left generator.
      -> Generator s2 m (Ann x2) -- ^ The right generator.
      -> [((Ann x1, Expr s1 m), (Ann x2, Expr s2 m))]
pairs including tier g1 g2 =
  [ (e1, e2)
  | e1 <- fromMaybe [] (getTier tier g1)
  , isSmallest (fst e1)
  , t  <- if including then [0..tier] else [0..tier - 1]
  , e2 <- fromMaybe [] (getTier t    g2)
  , isSmallest (fst e2)
  ]

-- | Filter for term generation: only generate binds out of smallest
-- terms.
checkGenBind :: Ann x -> Ann x -> Expr s m -> Bool
checkGenBind ann1 ann2 expr = case unBind expr of
  Just ("_", _, _) -> isSmallest ann1 && isSmallest ann2
  Just _ -> isSmallest ann2
  _ -> True

-- | Number of variants of a value to consider.
numVariants :: Int
numVariants = 10
