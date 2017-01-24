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
    -- * Observational refinement
  , refinesCC
  , equivalentCC
  ) where

import Control.Applicative ((<|>))
import Control.Arrow (second)
import Control.Monad ((<=<), join)
import Control.Monad.ST (ST)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Test.DejaFu (Failure, defaultBounds, defaultMemType)
import Test.DejaFu.Conc (ConcST)
import Test.DejaFu.SCT (sctBound)

import Test.Spec.Expr (Expr, ($$), bind, exprSize, rename, stateVariable)
import Test.Spec.Gen (Generator, newGenerator, stepGenerator, filterTier, getTier)

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
    check acc@(g1, g2) (a, b) = case (evalA a, evalB b) of
      (Just eval_a, Just eval_b) -> do
        refines_ab <- refinesAB (commute . eval_a) (commute . eval_b)
        refines_ba <- refinesBA (commute . eval_b) (commute . eval_a)
        let (g1', g2', obs) = mkobservation refines_ab refines_ba g1 g2 a b
        pure ((fromMaybe g1 g1', fromMaybe g2 g2'), obs)
      (_,_) -> pure (acc, Nothing)

    evalA a = eval exprs1 =<< bind "" a =<< (observation exprs1 $$ stateVariable)
    evalB b = eval exprs2 =<< bind "" b =<< (observation exprs2 $$ stateVariable)

    refinesAB a b = refinesCC (initialState exprs1) (initialState exprs2) a b seed
    refinesBA b a = refinesCC (initialState exprs2) (initialState exprs1) b a seed

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
                -> ST t (Generator s (ConcST t), [Observation])
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
    check g (a, b) = case (evalExpr a, evalExpr b) of
      (Just eval_a, Just eval_b) -> do
        refines_ab <- (commute . eval_a) `refines` (commute . eval_b)
        refines_ba <- (commute . eval_b) `refines` (commute . eval_a)
        let (g1', g2', obs) = mkobservation refines_ab refines_ba g g a b
        pure (fromMaybe g (g1' <|> g2'), obs)
      (_,_) -> pure (g, Nothing)

    evalExpr a = eval exprs =<< bind "" a =<< (observation exprs $$ stateVariable)
    refines a b = refinesCC (initialState exprs) (initialState exprs) a b seed


-------------------------------------------------------------------------------
-- Observational refinement

-- | Check if left concurrent expression is a refinement of the right.
--
-- Observational refinement is typically read as \"being more
-- deterministic than\" (or perhaps more accurately \"being at most as
-- nondeterministic as\").  \"@P@ refines @Q@\", written @P ⊑ Q@,
-- means that all behaviours of @P@ are possible behaviours of @Q@, up
-- to some observation.  For example, an observation we might take of
-- a stack is converting it to a list.
refinesCC :: Ord x
          => (a -> ConcST t cL) -- ^ Produce a new concurrent value of the left kind.
          -> (a -> ConcST t cR) -- ^ Produce a new concurrent value of the right kind.
          -> (cL -> ConcST t x) -- ^ Operation and observation on the left concurrent representation.
          -> (cR -> ConcST t x) -- ^ Operation and observation on the right concurrent representation.
          -> a
          -> ST t Bool
refinesCC mk_cL mk_cR obs_op_cL obs_op_cR seed = do
  cL_res <- runConc $ (obs_op_cL <=< mk_cL) seed
  cR_res <- runConc $ (obs_op_cR <=< mk_cR) seed
  pure (cL_res `S.isSubsetOf` cR_res)

-- | If we have @P ⊑ Q ∧ Q ⊑ P@, then @P@ and @Q@ are equivalent, up
-- to the provided observation.
equivalentCC :: Ord x
             => (a -> ConcST t c1) -- ^ Produce a new concurrent value of the first kind.
             -> (a -> ConcST t c2) -- ^ Produce a new concurrent value of the second kind.
             -> (c1 -> ConcST t x) -- ^ Operation and observation on the first concurrent representation.
             -> (c2 -> ConcST t x) -- ^ Operation and observation on the second concurrent representation.
             -> a
             -> ST t Bool
equivalentCC mk_c1 mk_c2 obs_op_c1 obs_op_c2 seed =
  (&&) <$> refinesCC mk_c1 mk_c2 obs_op_c1 obs_op_c2 seed
       <*> refinesCC mk_c2 mk_c1 obs_op_c2 obs_op_c1 seed


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
-- appropriate 'Observation' given the result of checking refinement.
mkobservation :: Bool -- ^ Whether the left refines the right.
              -> Bool -- ^ Whether the right refines the left.
              -> Generator s1 m -- ^ The left generator.
              -> Generator s2 m -- ^ The right generator.
              -> Expr s1 m -- ^ The left expression.
              -> Expr s2 m -- ^ The right expression.
              -> (Maybe (Generator s1 m), Maybe (Generator s2 m), Maybe Observation)
mkobservation refines_ab refines_ba g1 g2 a b =
  let (g1', g2') = if refines_ab || refines_ba
                   then if exprSize a >= exprSize b
                        then (Just $ filterTier (/=a) (exprSize a) g1, Nothing)
                        else (Nothing, Just $ filterTier (/=b) (exprSize b) g2)
        else (Nothing, Nothing)

      obs = if
        | refines_ab && refines_ba -> Just $
          if exprSize a > exprSize b then Equiv b a else Equiv a b
        | refines_ab -> Just (Refines a b)
        | refines_ba -> Just (Refines b a)
        | otherwise -> Nothing
  in (g1', g2', obs)

-- | Helper for 'discover' and 'discoverSingle': find pairs of
-- expressions to try checking for equality and refinement.
pairs :: Int -- ^ The current tier.
      -> Generator s1 m -- ^ The left generator.
      -> Generator s2 m -- ^ The right generator.
      -> [(Expr s1 m, Expr s2 m)]
pairs tier g1 g2 =
  [ (e1, e2)
  | e1 <- fromMaybe [] (getTier tier g1)
  , t  <- [0..tier - 1]
  , e2 <- fromMaybe [] (getTier t    g2)
  ]
