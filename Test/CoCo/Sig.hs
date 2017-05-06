-- |
-- Module      : Test.CoCo.Sig
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- Expression signatures for property discovery.
module Test.CoCo.Sig where

import Data.List (nub)
import Data.Typeable (Typeable, TypeRep)

import Test.CoCo.Expr (Schema, holeOf, unLit, stateVar)
import Test.CoCo.Type (dynTypeRep, funTys)
import Test.CoCo.Monad (Concurrency)

-- | A collection of expressions.
data Sig s o x = Sig
  { initialState :: x -> Concurrency s
  -- ^ Create a new instance of the state variable.
  , expressions :: [Schema s]
  -- ^ The primitive expressions to use.
  , backgroundExpressions :: [Schema s]
  -- ^ Expressions to use as helpers for building new
  -- expressions. Observations will not be reported about terms which
  -- are entirely composed of background expressions.
  , observation :: s -> x -> Concurrency o
  -- ^ The observation to make.
  , backToSeed :: s -> x -> Concurrency x
  -- ^ Convert the state back to the seed (used to determine if a term
  -- is boring).
  , setState :: s -> x -> Concurrency ()
  -- ^ Set the state value. This doesn't need to be atomic, or even
  -- guaranteed to work, its purpose is to cause interference when
  -- evaluating other terms.
  }

-- | Complete a signature: add missing holes and the state variable to
-- the background.
complete :: Typeable s => Sig s o x -> Sig s o x
complete sig =
  let state = [ stateVar
              | stateVar `notElem` expressions           sig
              , stateVar `notElem` backgroundExpressions sig
              ]
      holes = [ h
              | h <- map holeOf (inferHoles sig)
              , h `notElem` expressions           sig
              , h `notElem` backgroundExpressions sig
              ]
  in sig { backgroundExpressions = state ++ holes ++ backgroundExpressions sig }

-- | Infer necessary hole types in a signature.
inferHoles :: Sig s o x -> [TypeRep]
inferHoles sig = nub $ concatMap holesFor (expressions sig) ++ concatMap holesFor (backgroundExpressions sig) where
  holesFor = maybe [] (funTyHoles . dynTypeRep . snd) . unLit
  funTyHoles ty = case funTys ty of
    Just (argTy, resultTy) -> argTy : funTyHoles resultTy
    Nothing -> []
