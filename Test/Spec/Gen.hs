-- |
-- Module      : Test.Spec.Gen
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- Generating well-typed dynamic expressions from smaller components.
--
-- @
-- > :{
-- let baseTerms = [ constant "putMVar_int"  (putMVar  :: MVar Int -> Int -> IO ())
--                 , constant "takeMVar_int" (takeMVar :: MVar Int -> IO Int)
--                 , constant "readMVar_int" (readMVar :: MVar Int -> IO Int)
--                 , constant "succ_int"     (succ     :: Int -> Int)
--                 , variable "x"            (Proxy    :: Proxy Int)
--                 , stateVariable
--                 ] :: [Expr (MVar Int) IO]
-- :}
-- > mapM_ print . (!!8) $ enumerate baseTerms
-- succ_int (succ_int (succ_int (succ_int x)))
-- putMVar_int :state: (succ_int (succ_int x))
-- takeMVar_int :state: >>= \\_ -> putMVar_int :state: x
-- takeMVar_int :state: >>= \\x' -> putMVar_int :state: x'
-- readMVar_int :state: >>= \\_ -> putMVar_int :state: x
-- readMVar_int :state: >>= \\x' -> putMVar_int :state: x'
-- putMVar_int :state: x >>= \\_ -> takeMVar_int :state:
-- putMVar_int :state: x >>= \\_ -> readMVar_int :state:
-- @
module Test.Spec.Gen
  ( -- * Generating Terms
    enumerate

  -- ** Controlled generation
  , Generator
  , newGenerator
  , stepGenerator
  , getTier
  , mapTier
  , maxTier
  ) where

import qualified Data.IntMap as M
import Data.Maybe (catMaybes, fromMaybe, isJust)
import qualified Data.Set as S

import Test.Spec.Expr
import Test.Spec.Type (unmonad)

-- | Enumerate all well-typed expressions, in size order.
enumerate :: [Expr s m] -> [[Expr s m]]
enumerate = tail . go 0 . newGenerator where
  go tier g =
    fromMaybe [] (getTier tier g) : go (tier+1) (stepGenerator g)


-------------------------------------------------------------------------------
-- Controlled generation

-- | A generator of expressions.
data Generator s m = Generator { tiers :: M.IntMap [Expr s m], sofar :: Int }
  deriving Eq

-- | Create a new generator from a collection of basic expressions.
newGenerator :: [Expr s m] -> Generator s m
newGenerator baseTerms = Generator
  { tiers = merge [M.fromList [(exprSize t, [t])] | t <- baseTerms]
  , sofar = 0
  }

-- | Generate the next tier.
stepGenerator :: Generator s m -> Generator s m
stepGenerator g = Generator newTiers (sofar g + 1) where
  newTiers =
    let new = merge [ tiers g
                    , M.singleton (sofar g + 1) funAps
                    , M.singleton (sofar g + 1) binds
                    , M.singleton (sofar g + 1) lets
                    ]
    in M.adjust (prune new) (sofar g + 1) new

  -- produce new terms by function application.
  funAps = mkTerms $ \terms candidates ->
    [ t1 $$ t2 | t1 <- terms, exprTypeArity t1 > 0, t2 <- candidates]

  -- produce new terms by monad-binding variables.
  binds = mkTerms $ \terms candidates ->
    [bind var t1 t2 | t1 <- terms, isJust . unmonad $ exprTypeRep t1, t2 <- candidates, var <- "_" : map fst (freeVariables t2)]

  -- produce new terms by let-binding variables.
  lets = mkTerms $ \terms candidates ->
    [let_ var t1 t2 | t1 <- terms, not (isVariable t1), t2 <- candidates, not (isVariable t2), (var,_) <- freeVariables t2]

  -- produce new terms
  mkTerms f = M.foldMapWithKey go (tiers g) where
    go tier terms =
      let candidates = sizedTerms (sofar g - tier) (tiers g)
      in catMaybes (f terms candidates)

  -- prune uninteresting expressions.
  prune tieredTerms = filter go . ordNub where
    go term
      | isLet term =
        let term' = assignLets term
        in term' `notElem` sizedTerms (exprSize term') tieredTerms
      | otherwise = True

  -- get all terms of the given size.
  sizedTerms = M.findWithDefault []

-- | Get the terms of a given size, if they have been generated.
getTier :: Int -> Generator s m -> Maybe [Expr s m]
getTier tier g
  -- this check is to avoid returning a partial result, which is
  -- possible as the tiers are initially populated based on the base
  -- terms.
  | tier > sofar g = Nothing
  | otherwise = M.lookup tier (tiers g)

-- | Apply a function to the terms in a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
mapTier :: ([Expr s m] -> [Expr s m]) -> Int -> Generator s m -> Generator s m
mapTier f tier g = g { tiers = M.adjust f tier (tiers g) }

-- | Get the highest size generated so far.
maxTier :: Generator s m -> Int
maxTier = sofar


-------------------------------------------------------------------------------
-- Utilities

-- | Merge a list of maps of lists.
merge :: [M.IntMap [a]] -> M.IntMap [a]
merge = M.unionsWith (++)

-- | Remove duplicates from a list efficiently.
ordNub :: Ord a => [a] -> [a]
ordNub = go S.empty where
  go _ [] = []
  go s (x:xs)
    | x `S.member` s = go s xs
    | otherwise = x : go (S.insert x s) xs
