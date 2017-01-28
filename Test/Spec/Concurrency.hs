{-# LANGUAGE GADTs #-}

-- |
-- Module      : Test.Spec.Concurrency
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs
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
  -- * Building blocks
  , (|||)
  ) where

import Control.Arrow (second)
import qualified Control.Concurrent.Classy as C
import Control.Monad (join)
import Control.Monad.ST (ST)
import Data.Either (isLeft)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Semigroup (Semigroup(..))
import Data.Set (Set)
import qualified Data.Set as S
import Test.DejaFu (Failure, defaultBounds, defaultMemType)
import Test.DejaFu.Conc (ConcST)
import Test.DejaFu.SCT (sctBound)

import Test.Spec.Expr (Expr, ($$), bind, exprSize, exprTypeRep, rename, stateVariable, unBind)
import Test.Spec.Gen (Generator, newGenerator', stepGenerator, filterTier, getTier, mapTier)

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
  , eval :: Expr s m -> Maybe (s -> m (Maybe (m x)))
  -- ^ Evaluate an expression. In practice this will just be
  -- @evaluate@ from "Test.Spec.Expr", but it's here to make the types
  -- work out.
  }

-- | Attempt to discover properties of the given set of concurrent operations.
discover :: Ord x
         => Exprs s1 (ConcST t) x a -- ^ A collection of expressions
         -> Exprs s2 (ConcST t) x a -- ^ Another collection of expressions.
         -> a   -- ^ Seed for the state variable
         -> Int -- ^ Term size limit
         -> ST t [Observation]
discover exprs1 exprs2 seed lim = do
    (g1, _) <- discoverSingle' exprs1 seed lim
    (g2, _) <- discoverSingle' exprs2 seed lim
    concat <$> findObservations 0 g1 g2
  where
    -- check every pair of terms (in size order) for equality and
    -- refinement with the smaller terms.
    findObservations tier g1 g2 = do
      ((g1', g2'), observations) <- mapAccumLM check (g1, g2) (pairs tier g1 g2)
      (catMaybes observations:) <$> if tier == lim
        then pure []
        else findObservations (tier+1) g1' g2'

    -- check if a pair of terms are observationally equal, or if one
    -- is a refinement of the other.
    check acc@(g1, g2) ((ann_a, expr_a), (ann_b, expr_b)) = case (evalA expr_a, evalB expr_b) of
      (Just eval_a, Just eval_b) -> do
        results_a <- runConc $ commute . eval_a =<< initialState exprs1 seed
        results_b <- runConc $ commute . eval_b =<< initialState exprs2 seed

        -- if an expression always fails, record that.
        let g1' = annotate expr_a (\ann -> ann { isFailing = all isLeft results_a }) g1
        let g2' = annotate expr_b (\ann -> ann { isFailing = all isLeft results_b }) g2

        let (g12'', obs) = mkobservation False results_a results_b g1' g2' expr_a expr_b ann_a ann_b

        -- get the updated generators
        let g1'' = maybe g1' (either id (const g1')) g12''
        let g2'' = maybe g2' (either (const g2') id) g12''

        pure ((g1'', g2''), obs)
      (_,_) -> pure (acc, Nothing)

    evalA e = eval exprs1 =<< bind "" e =<< (observation exprs1 $$ stateVariable)
    evalB e = eval exprs2 =<< bind "" e =<< (observation exprs2 $$ stateVariable)

-- | Like 'discover', but only takes a single set of expressions. This
-- will lead to better pruning.
discoverSingle :: Ord x
               => Exprs s (ConcST t) x a
               -> a
               -> Int
               -> ST t [Observation]
discoverSingle exprs seed lim = snd <$> discoverSingle' exprs seed lim

-- | 'discoverSingle' but also returns the 'Generator'.
discoverSingle' :: Ord x
                => Exprs s (ConcST t) x a
                -> a
                -> Int
                -> ST t (Generator s (ConcST t) Ann, [Observation])
discoverSingle' exprs seed lim =
    let g = newGenerator' [(initialAnn, e) | e <- expressions exprs]
    in second concat <$> findObservations 0 g
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations tier g = do
      (g', observations) <- mapAccumLM check g (pairs tier g g)
      second (catMaybes observations:) <$> if tier == lim
        then pure (g', [])
        else findObservations (tier+1) (stepGenerator checkGenBind g')

    -- check if a pair of terms are observationally equal, or if one
    -- is a refinement of the other.
    check g ((ann_a, expr_a), (ann_b, expr_b)) = case (evalExpr expr_a, evalExpr expr_b) of
      (Just eval_a, Just eval_b) -> do
        results_a <- runConc $ commute . eval_a =<< initialState exprs seed
        results_b <- runConc $ commute . eval_b =<< initialState exprs seed

        -- if an expression always fails, record that.
        let g' = annotate expr_a (\ann -> ann { isFailing = all isLeft results_a }) $
                 annotate expr_b (\ann -> ann { isFailing = all isLeft results_b }) g

        let (g'', obs) = mkobservation (exprTypeRep expr_a == exprTypeRep expr_b) results_a results_b g' g' expr_a expr_b ann_a ann_b
        pure (maybe g' (either id id) g'', obs)
      (_,_) -> pure (g, Nothing)

    evalExpr e = eval exprs =<< bind "" e =<< (observation exprs $$ stateVariable)

    checkGenBind (ann1, _) (ann2, _) (_, expr) = case unBind expr of
      Just ("_", _, _) -> isSmallest ann1 && isSmallest ann2
      Just _ -> isSmallest ann2
      _ -> True


-------------------------------------------------------------------------------
-- Annotations

-- | An annotation on an expression.
--
-- The 'Semigroup' instance is very optimistic, and assumes that
-- combining two expressions will yield the smallest in its new
-- equivalence class (which means there is no unit). It is the job of
-- 'mkobservation' to crush these dreams.
data Ann = Ann
  { isFailing  :: Bool
  , isSmallest :: Bool
  }
  deriving (Eq, Ord, Read, Show)

instance Semigroup Ann where
  ann1 <> ann2 = Ann { isFailing  = isFailing ann1 || isFailing ann2
                     , isSmallest = True
                     }

-- | The \"default\" annotation. This is not the unit of
-- 'Semigroup.<>', as it has no unit.
initialAnn :: Ann
initialAnn = Ann { isFailing = False, isSmallest = True }

-- | Annotate an expression.
annotate :: Expr s m -> (ann -> ann) -> Generator s m ann -> Generator s m ann
annotate expr f = mapTier go (exprSize expr) where
  go (ann0, expr0) = (if expr0 == expr then f ann0 else ann0, expr0)


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

-- | Run a concurrent computation, producing the set of all results.
runConc :: Ord a => ConcST t a -> ST t (Set (Either Failure a))
runConc c =
  S.fromList . map fst <$> sctBound defaultMemType defaultBounds c

-- | Commute and join monads.
commute :: Monad m => m (Maybe (m a)) -> m (Maybe a)
commute = join . fmap (maybe (pure Nothing) (fmap Just))

-- | Monadic version of 'mapAccumL' specialised to lists.
mapAccumLM :: Monad m
           => (a -> b -> m (a, c))
           -> a
           -> [b]
           -> m (a, [c])
mapAccumLM _ s []     = pure (s, [])
mapAccumLM f s (x:xs) = do
  (s1, x')  <- f s x
  (s2, xs') <- mapAccumLM f s1 xs
  pure (s2, x' : xs')

-- | Helper for 'discover' and 'discoverSingle': construct an
-- appropriate 'Observation' given the results of execution. The left
-- and right annotations may have been changed: this is used to
-- determine if a failure is interesting or not.
--
-- TODO: This is pretty messy, combining the annotation changes with
-- the observation. Maybe better to split it up?
mkobservation :: Ord x
              => Bool -- ^ Whether the expressions are the same type.
              -> Set (Either Failure x) -- ^ The left results.
              -> Set (Either Failure x) -- ^ The right results.
              -> Generator s1 m Ann -- ^ The left generator.
              -> Generator s2 m Ann -- ^ The right generator.
              -> Expr s1 m -- ^ The left expression.
              -> Expr s2 m -- ^ The right expression.
              -> Ann -- ^ The original left annotation.
              -> Ann -- ^ The original right annotation.
              -> (Maybe (Either (Generator s1 m Ann) (Generator s2 m Ann)), Maybe Observation)
mkobservation same_type results_a results_b g1 g2 expr_a expr_b ann_a ann_b = (g12', obs) where
  -- a failure is uninteresting if the failing term is built out of failing components
  uninteresting_failure
    | exprSize expr_a >= exprSize expr_b = all isLeft results_a && isFailing ann_a
    | otherwise = all isLeft results_b && isFailing ann_b

  -- P ⊑ Q iff the results of P are a subset of the results of Q
  refines_ab = results_a `S.isSubsetOf` results_b
  refines_ba = results_b `S.isSubsetOf` results_a

  -- if there is a refinement, remove the larger expression from the generator
  g12'
    | refines_ab && (not refines_ba || refines_ba && exprSize expr_b >= exprSize expr_a) =
      Just . Right $ if same_type
                     then filterTier ((/=expr_b) . snd) (exprSize expr_b) g2
                     else annotate expr_b (\ann -> ann { isSmallest = False }) g2
    | refines_ba && (not refines_ab || refines_ab && exprSize expr_a >= exprSize expr_b) =
      Just . Left  $ if same_type
                     then filterTier ((/=expr_a) . snd) (exprSize expr_a) g1
                     else annotate expr_a (\ann -> ann { isSmallest = False }) g1
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
pairs :: Int -- ^ The current tier.
      -> Generator s1 m Ann -- ^ The left generator.
      -> Generator s2 m Ann -- ^ The right generator.
      -> [((Ann, Expr s1 m), (Ann, Expr s2 m))]
pairs tier g1 g2 =
  [ (e1, e2)
  | e1 <- fromMaybe [] (getTier tier g1)
  , isSmallest (fst e1)
  , t  <- [0..tier - 1]
  , e2 <- fromMaybe [] (getTier t    g2)
  , isSmallest (fst e2)
  ]
