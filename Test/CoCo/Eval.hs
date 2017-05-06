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
import Control.DeepSeq (NFData, force)
import qualified Data.List.NonEmpty as L
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Set as S
import qualified Data.Typeable as T
import Test.DejaFu.Common (ThreadAction(..))

import Test.CoCo.Ann
import Test.CoCo.Expr (Term, bind, lit, environment, evaluate)
import Test.CoCo.Type (Dynamic, coerceDyn, coerceTypeRep, rawTypeRep)
import Test.CoCo.TypeInfo (TypeInfo(..), getTypeValues)
import Test.CoCo.Util
import Test.CoCo.Monad

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
  -> (x -> Concurrency s)
  -- ^ Create a new instance of the state variable.
  -> Maybe (s -> x -> Concurrency ())
  -- ^ State interference function, if applicable.
  -> (s -> x -> Concurrency o)
  -- ^ The observation to make.
  -> (s -> x -> Concurrency x)
  -- ^ Convert the state back to the seed.
  -> [x]
  -- ^ The seed values to use.
  -> Term s Concurrency
  -- ^ The term to evaluate.  This must have a monadic result type.
  -> Maybe (Bool, VarResults o x)
runSingle typeInfos mkstate interfere observe unstate seeds expr
    | null assignments = Nothing
    | otherwise = Just $
        let out = (and *** L.fromList) . unzip $ map go assignments
        in force out
  where
    assignments = varassigns typeInfos seeds expr

    go (varassign, eval_expr) =
      let -- the results
        rs = runSCT' $ do
          let x = seedVal varassign
          s <- mkstate x
          r <- subconcurrency $ case interfere of
            Just interfereFunc -> do
              i <- C.spawn (interfereFunc s x)
              o <- shoveMaybe (eval_expr s)
              C.readMVar i
              pure o
            Nothing ->
              shoveMaybe (eval_expr s)
          o  <- observe s x
          x' <- unstate s x
          pure (either Just (const Nothing) r, x', o)

        -- very rough interpretation of atomicity: the trace has one
        -- thing in it other than the stop!
        is_atomic trc =
          let relevant = filter (\(_,_,ta) -> ta /= Return) .
                         takeWhile (\(_,_,ta) -> ta /= StopSubconcurrency && ta /= Stop) .
                         drop 1 .
                         dropWhile (\(_,_,ta) -> ta /= Subconcurrency)
          in length (relevant trc) == 1

        -- the output
        out = (all (is_atomic . snd) rs, (varassign, smapMaybe eitherToMaybe . S.fromList $ map fst rs))

      -- strictify, to avoid wasting memory on intermediate results.
      in force out

-- | Produce a list of variable assignments for the seed and free
-- variables in a term.  This produces both a 'VarAssign' and the term
-- evaluation.
--
-- 'numVariants' values will be taken of each and zipped together
-- (producing @numVariants^(length (environment term) + 1)@
-- assignments).
varassigns :: forall s x.
     [(T.TypeRep, TypeInfo)]
  -- ^ Information about types.  There MUST be an entry for every hole
  -- type!
  -> [x]
  -- ^ The seed values to use.
  -> Term s Concurrency
  -- ^ The term to evaluate.  This must have a result in the monad.
  -> [(VarAssignment x, s -> Maybe (Concurrency ()))]
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

    evoid :: Term s Concurrency -> Maybe (Term s Concurrency)
    evoid e = bind [] e (lit "" (pure () :: Concurrency ()))

    enumerateValues = getTypeValues typeInfos . rawTypeRep

    eval :: (Term s Concurrency -> [(String, Dynamic s Concurrency)] -> Maybe (s -> Maybe (Concurrency ())))
    eval = evaluate

-- | Number of variants of a value to consider.
numVariants :: Int
numVariants = 10
