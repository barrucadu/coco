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
-- takeMVar_int :state: >> putMVar_int :state: x
-- takeMVar_int :state: >>= \\x' -> putMVar_int :state: x'
-- readMVar_int :state: >> putMVar_int :state: x
-- readMVar_int :state: >>= \\x' -> putMVar_int :state: x'
-- putMVar_int :state: x >> takeMVar_int :state:
-- putMVar_int :state: x >> readMVar_int :state:
-- @
module Test.Spec.Gen
  ( -- * Generating Terms
    enumerate

  -- ** Controlled generation
  , Generator
  , newGenerator
  , newGenerator'
  , stepGenerator
  , getTier
  , mapTier
  , filterTier
  , adjustTier
  , maxTier
  ) where

import qualified Data.IntMap as M
import Data.Maybe (isJust)
import Data.Semigroup (Semigroup, (<>))

import Test.Spec.Expr
import Test.Spec.Type (unmonad)
import Test.Spec.Util

-- | Enumerate all well-typed expressions, in size order.
enumerate :: [Expr s m] -> [[Expr s m]]
enumerate = tail . go 0 . newGenerator where
  go :: Int -> Generator s m () -> [[Expr s m]]
  go tier g =
    maybe [] (map snd) (getTier tier g) : go (tier+1) (stepGenerator (\_ _ _ -> True) g)


-------------------------------------------------------------------------------
-- Controlled generation

-- | A generator of expressions.
data Generator s m ann = Generator { tiers :: M.IntMap [(ann, Expr s m)], sofar :: Int }
  deriving Eq

-- | Create a new generator from a collection of basic expressions.
newGenerator :: Monoid ann => [Expr s m] -> Generator s m ann
newGenerator = newGenerator' . map (\e -> (mempty, e))

-- | Like 'newGenerator', but use an explicit default value.
newGenerator' :: [(ann, Expr s m)] -> Generator s m ann
newGenerator' baseTerms = Generator
  { tiers = merge [M.fromList [(exprSize (snd t), [t])] | t <- baseTerms]
  , sofar = 0
  }

-- | Generate the next tier.
stepGenerator :: Semigroup ann
              => ((ann, Expr s m) -> (ann, Expr s m) -> (ann, Expr s m) -> Bool)
              -- ^ First expr, second expr, combined expr.
              -> Generator s m ann -> Generator s m ann
stepGenerator check g = Generator newTiers (sofar g + 1) where
  newTiers =
    let new = merge [ tiers g
                    , M.singleton (sofar g + 1) funAps
                    , M.singleton (sofar g + 1) binds
                    , M.singleton (sofar g + 1) lets
                    ]
    in M.adjust (prune new) (sofar g + 1) new

  -- produce new terms by function application.
  funAps = mkTerms 0 $ \terms candidates ->
    [ (resAnn, resExpr) | t1@(a1, e1) <- terms
                        , exprTypeArity e1 > 0
                        , t2@(a2, e2) <- candidates
                        , (resAnn, Just resExpr) <- [(a1 <> a2, e1 $$ e2)]
                        , check t1 t2 (resAnn, resExpr)
    ]

  -- produce new terms by monad-binding variables.
  binds = mkTerms 1 $ \terms candidates ->
    [ (resAnn, resExpr) | t1@(a1, e1) <- terms
                        , isJust . unmonad $ exprTypeRep e1
                        , t2@(a2, e2) <- candidates
                        , var <- "_" : map fst (freeVariables e2)
                        , (resAnn, Just resExpr) <- [(a1 <> a2, bind var e1 e2)]
                        , check t1 t2 (resAnn, resExpr)
    ]

  -- produce new terms by let-binding variables.
  lets = mkTerms 1 $ \terms candidates ->
    [ (resAnn, resExpr) | t1@(a1, e1) <- terms
                        , not (isVariable e1)
                        , t2@(a2, e2) <- candidates
                        , not (isVariable e2)
                        , (var,_) <- freeVariables e2
                        , (resAnn, Just resExpr) <- [(a1 <> a2, let_ var e1 e2)]
                        , check t1 t2 (resAnn, resExpr)
    ]

  -- produce new terms
  mkTerms n f = M.foldMapWithKey go (tiers g) where
    go tier terms =
      let candidates = sizedTerms (sofar g + 1 - tier - n) (tiers g)
      in f terms candidates

  -- prune uninteresting expressions.
  prune tieredTerms = filter go . ordNubOn snd where
    go (_, term)
      | isLet term =
        let term' = assignLets term
        in term' `notElem` map snd (sizedTerms (exprSize term') tieredTerms)
      | otherwise = True

  -- get all terms of the given size.
  sizedTerms = M.findWithDefault []

-- | Get the terms of a given size, if they have been generated.
getTier :: Int -> Generator s m ann -> Maybe [(ann, Expr s m)]
getTier tier g
  -- this check is to avoid returning a partial result, which is
  -- possible as the tiers are initially populated based on the base
  -- terms.
  | tier > sofar g = Nothing
  | otherwise = M.lookup tier (tiers g)

-- | Apply a function to every expression in a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
mapTier :: ((ann, Expr s m) -> (ann, Expr s m)) -> Int -> Generator s m ann -> Generator s m ann
mapTier = adjustTier . map

-- | Filter expressions in a tier.
filterTier :: ((ann, Expr s m) -> Bool) -> Int -> Generator s m ann -> Generator s m ann
filterTier = adjustTier . filter

-- | Apply a function to a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
adjustTier :: ([(ann, Expr s m)] -> [(ann, Expr s m)]) -> Int -> Generator s m ann -> Generator s m ann
adjustTier f tier g = g { tiers = M.adjust f tier (tiers g) }

-- | Get the highest size generated so far.
maxTier :: Generator s m ann -> Int
maxTier = sofar


-------------------------------------------------------------------------------
-- Utilities

-- | Merge a list of maps of lists.
merge :: [M.IntMap [a]] -> M.IntMap [a]
merge = M.unionsWith (++)
