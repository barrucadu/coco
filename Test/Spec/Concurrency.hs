{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}

-- |
-- Module      : Test.Spec.Concurrency
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs, MultiWayIf
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
  ) where

import Control.Arrow (second)
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

import Test.Spec.Expr (Expr, ($$), bind, exprSize, rename, stateVariable)
import Test.Spec.Gen (Generator, newGenerator, stepGenerator, filterTier, getTier, mapTier)

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
        let g1' = annotate expr_a (if all isLeft results_a then Fails else ann_a) g1
        let g2' = annotate expr_b (if all isLeft results_b then Fails else ann_b) g2

        let (g12'', obs) = mkobservation results_a results_b g1' g2' expr_a expr_b ann_a ann_b

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
    let g = newGenerator (expressions exprs)
    in second concat <$> findObservations 0 g
  where
    -- check every term on the current tier for equality and
    -- refinement with the smaller terms.
    findObservations tier g = do
      (g', observations) <- mapAccumLM check g (pairs tier g g)
      second (catMaybes observations:) <$> if tier == lim
        then pure (g', [])
        else findObservations (tier+1) (stepGenerator g')

    -- check if a pair of terms are observationally equal, or if one
    -- is a refinement of the other.
    check g ((ann_a, expr_a), (ann_b, expr_b)) = case (evalExpr expr_a, evalExpr expr_b) of
      (Just eval_a, Just eval_b) -> do
        results_a <- runConc $ commute . eval_a =<< initialState exprs seed
        results_b <- runConc $ commute . eval_b =<< initialState exprs seed

        -- if an expression always fails, record that.
        let g' = annotate expr_a (if all isLeft results_a then Fails else ann_a) $
                 annotate expr_b (if all isLeft results_b then Fails else ann_b) g

        let (g'', obs) = mkobservation results_a results_b g' g' expr_a expr_b ann_a ann_b
        pure (maybe g' (either id id) g'', obs)
      (_,_) -> pure (g, Nothing)

    evalExpr e = eval exprs =<< bind "" e =<< (observation exprs $$ stateVariable)


-------------------------------------------------------------------------------
-- Annotations

-- | An annotation on an expression.
data Ann = Ok | Fails
  deriving (Eq, Ord, Read, Show, Bounded, Enum)

instance Semigroup Ann where
  Ok <> ann = ann
  ann <> Ok = ann
  _ <> _ = Fails

instance Monoid Ann where
  mappend = (<>)
  mempty = Ok

-- | Annotate an expression. This overwrites any previous annotation.
annotate :: Expr s m -> ann -> Generator s m ann -> Generator s m ann
annotate expr ann = mapTier go (exprSize expr) where
  go (ann0, expr0) = (if expr0 == expr then ann else ann0, expr0)


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
mkobservation :: Ord x
              => Set (Either Failure x) -- ^ The left results.
              -> Set (Either Failure x) -- ^ The right results.
              -> Generator s1 m Ann -- ^ The left generator.
              -> Generator s2 m Ann -- ^ The right generator.
              -> Expr s1 m -- ^ The left expression.
              -> Expr s2 m -- ^ The right expression.
              -> Ann -- ^ The original left annotation.
              -> Ann -- ^ The original right annotation.
              -> (Maybe (Either (Generator s1 m Ann) (Generator s2 m Ann)), Maybe Observation)
mkobservation results_a results_b g1 g2 expr_a expr_b ann_a ann_b = (g12', obs) where
  -- a failure is uninteresting if the failing term is built out of failing components
  uninteresting_failure
    | exprSize expr_a >= exprSize expr_b = all isLeft results_a && ann_a == Fails
    | otherwise = all isLeft results_b && ann_b == Fails

  -- P ⊑ Q iff the results of P are a subset of the results of Q
  refines_ab = results_a `S.isSubsetOf` results_b
  refines_ba = results_b `S.isSubsetOf` results_a

  -- if there is a refinement, remove the larger expression from the generator
  g12' = if refines_ab || refines_ba
         then if exprSize expr_a >= exprSize expr_b
              then Just . Left  $ filterTier ((/=expr_a) . snd) (exprSize expr_a) g1
              else Just . Right $ filterTier ((/=expr_b) . snd) (exprSize expr_b) g2
         else Nothing

  -- describe the observation
  obs = if
    | uninteresting_failure -> Nothing
    | refines_ab && refines_ba -> Just $
      if exprSize expr_a > exprSize expr_b then Equiv expr_b expr_a else Equiv expr_a expr_b
    | refines_ab -> Just (Refines expr_a expr_b)
    | refines_ba -> Just (Refines expr_b expr_a)
    | otherwise -> Nothing

-- | Helper for 'discover' and 'discoverSingle': find pairs of
-- expressions to try checking for equality and refinement.
pairs :: Int -- ^ The current tier.
      -> Generator s1 m ann1 -- ^ The left generator.
      -> Generator s2 m ann2 -- ^ The right generator.
      -> [((ann1, Expr s1 m), (ann2, Expr s2 m))]
pairs tier g1 g2 =
  [ (e1, e2)
  | e1 <- fromMaybe [] (getTier tier g1)
  , t  <- [0..tier - 1]
  , e2 <- fromMaybe [] (getTier t    g2)
  ]
