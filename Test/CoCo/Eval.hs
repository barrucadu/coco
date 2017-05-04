{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Test.CoCo.Eval
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ScopedTypeVariables
--
-- Evaluate concurrency terms.
module Test.CoCo.Eval where

import Control.Arrow ((***), second)
import qualified Control.Concurrent.Classy as C
import Control.DeepSeq (NFData, rnf)
import Control.Monad.ST (ST)
import qualified Data.List.NonEmpty as L
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Set as S
import qualified Data.Typeable as T
import Test.DejaFu (defaultMemType, defaultWay)
import Test.DejaFu.Common (ThreadAction(..))
import Test.DejaFu.Conc (ConcST, subconcurrency)
import Test.DejaFu.SCT (runSCT')

import Test.CoCo.Ann
import Test.CoCo.Expr (Term, bind, lit, environment, evaluate)
import Test.CoCo.Type (Dynamic, coerceDyn, coerceTypeRep, rawTypeRep)
import Test.CoCo.TypeInfo (TypeInfo(..), getTypeValues)
import Test.CoCo.Util

-- | Run a concurrent program many times, gathering the results.  Up
-- to 'numVariants' values of every free variable, including the seed,
-- are tried in all combinations.
--
-- The @Bool@ in the return value is whether the execution of this
-- term is atomic.
runSingle :: (Ord x, NFData o, NFData x, Ord o)
  => [(T.TypeRep, TypeInfo)]
  -- ^ Information about types.  There MUST be an entry for every hole
  -- type!
  -> (x -> ConcST t s)
  -- ^ Create a new instance of the state variable.
  -> Maybe (s -> x -> ConcST t ())
  -- ^ State interference function, if applicable.
  -> (s -> ConcST t o)
  -- ^ The observation to make.
  -> (s -> ConcST t x)
  -- ^ Convert the state back to the seed.
  -> [x]
  -- ^ The seed values to use.
  -> Term s (ConcST t)
  -- ^ The term to evaluate.  This must have a monadic result type.
  -> Maybe (ST t (Bool, VarResults o x))
runSingle typeInfos mkstate interfere observe unstate seeds expr
    | null assignments = Nothing
    | otherwise = Just $ do
        out <- (and *** L.fromList) . unzip <$> mapM go assignments
        rnf out `seq` pure out
  where
    assignments = varassigns typeInfos seeds expr

    go (varassign, eval_expr) = do
      rs <- runSCT' defaultWay defaultMemType $ do
        s <- mkstate (seedVal varassign)
        r <- subconcurrency $ case interfere of
          Just interfereFunc -> do
            i <- C.spawn . interfereFunc s $ seedVal varassign
            o <- shoveMaybe (eval_expr s)
            C.readMVar i
            pure o
          Nothing ->
            shoveMaybe (eval_expr s)
        o  <- observe s
        x' <- unstate s
        pure (either Just (const Nothing) r, x', o)
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

-- | Produce a list of variable assignments for the seed and free
-- variables in a term.  This produces both a 'VarAssign' and the term
-- evaluation.
--
-- 'numVariants' values will be taken of each and zipped together
-- (producing @numVariants^(length (environment term) + 1)@
-- assignments).
varassigns :: forall s t x.
     [(T.TypeRep, TypeInfo)]
  -- ^ Information about types.  There MUST be an entry for every hole
  -- type!
  -> [x]
  -- ^ The seed values to use.
  -> Term s (ConcST t)
  -- ^ The term to evaluate.  This must have a result in the monad.
  -> [(VarAssignment x, s -> Maybe (ConcST t ()))]
varassigns typeInfos seeds term =
    [ (VA seed (M.fromList vidmap), eval_term)
    | seed <- take numVariants seeds
    , (vidmap, eval_term) <- assign [] vars term
    ]
  where
    assign env ((var, dyns):free) e =
      [ ((var, vid):vidlist, eval_term)
      | (vid, Just dyn) <- map (second coerceDyn) . take numVariants $ zip [0..] dyns
      , (vidlist, eval_term) <- assign ((var, dyn):env) free e
      ]
    assign env [] e = maybeToList $ (\r -> ([], r)) <$> (evoid e >>= \e' -> eval e' env)

    vars = ordNubOn fst (map (second enumerateValues) (freeVars term))
    freeVars = mapMaybe (\(var, ty) -> (,) <$> pure var <*> coerceTypeRep ty) . environment

    evoid :: Term s (ConcST t) -> Maybe (Term s (ConcST t))
    evoid e = bind [] e (lit "" (pure () :: ConcST t ()))

    enumerateValues = getTypeValues typeInfos . rawTypeRep

    eval :: (Term s (ConcST t) -> [(String, Dynamic s (ConcST t))] -> Maybe (s -> Maybe (ConcST t ())))
    eval = evaluate

-- | Number of variants of a value to consider.
numVariants :: Int
numVariants = 10
