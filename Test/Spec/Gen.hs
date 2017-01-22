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
module Test.Spec.Gen where

import Data.List (mapAccumL)
import qualified Data.IntMap as M
import Data.Maybe (catMaybes, isJust)

import Test.Spec.Expr
import Test.Spec.Type (unmonad)

-- | Enumerate all well-typed expressions, in size order.
enumerate :: [Expr s m] -> [[Expr s m]]
enumerate baseTerms = snd (mapAccumL genTier initialTerms [1..]) where
  -- generate a map of initial terms
  initialTerms = termsList [M.fromList [(exprSize t, [t])] | t <- baseTerms]

  -- given a list of terms generated so far, and a size limit, combine
  -- the terms to produce new ones which fit into the limit, emitting
  -- all without free variables as the terms for this size-tier.
  genTier tieredTerms size =
    let newTiers = termsList [ tieredTerms
                             , M.singleton size (genFunAps tieredTerms size)
                             , M.singleton size (genBinds  tieredTerms size)
                             , M.singleton size (genLets   tieredTerms size)
                             ]
        newTiers' = M.adjust (prune newTiers) size newTiers
    in (newTiers', sizedTerms size newTiers')

  -- produce new terms by function application.
  genFunAps = mkTerms $ \terms candidates ->
    [ t1 $$ t2 | t1 <- terms, exprTypeArity t1 > 0, t2 <- candidates]

  -- produce new terms by monad-binding variables.
  genBinds = mkTerms $ \terms candidates ->
    [bind var t1 t2 | t1 <- terms, isJust . unmonad $ exprTypeRep t1, t2 <- candidates, var <- "_" : map fst (freeVariables t2)]

  -- produce new terms by let-binding variables.
  genLets = mkTerms $ \terms candidates ->
    [let_ var t1 t2 | t1 <- terms, not (isVariable t1), t2 <- candidates, not (isVariable t2), (var,_) <- freeVariables t2]

  -- produce new terms
  mkTerms f tieredTerms size = M.foldMapWithKey go tieredTerms where
    go tier terms =
      let candidates = sizedTerms (size - tier - 1) tieredTerms
      in catMaybes (f terms candidates)

  -- prune uninteresting expressions.
  prune tieredTerms = filter go where
    go term
      | isLet term =
        let term' = assignLets term
        in term' `notElem` sizedTerms (exprSize term') tieredTerms
      | otherwise = case filter (\t -> t /= term && t `alphaEq` term) (sizedTerms (exprSize term) tieredTerms) of
          [] -> True
          eqs -> term < minimum eqs

  -- merge a list of maps of terms-by-size into a map of lists of
  -- terms-by-size.
  termsList = M.unionsWith (++)

  -- get all terms of the given size.
  sizedTerms = M.findWithDefault []
