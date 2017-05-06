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

-- | A collection of expressions.
data Sig s m o x = Sig
  { initialState :: x -> m s
  -- ^ Create a new instance of the state variable.
  , expressions :: [Schema s m]
  -- ^ The primitive expressions to use.
  , backgroundExpressions :: [Schema s m]
  -- ^ Expressions to use as helpers for building new
  -- expressions. Observations will not be reported about terms which
  -- are entirely composed of background expressions.
  , observation :: s -> x -> m o
  -- ^ The observation to make.
  , backToSeed :: s -> x -> m x
  -- ^ Convert the state back to the seed (used to determine if a term
  -- is boring).
  , setState :: s -> x -> m ()
  -- ^ Set the state value. This doesn't need to be atomic, or even
  -- guaranteed to work, its purpose is to cause interference when
  -- evaluating other terms.
  }

-- | Complete a signature: add missing holes and the state variable to
-- the background.
complete :: Typeable s => Sig s m o x -> Sig s m o x
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
inferHoles :: Sig s m o x -> [TypeRep]
inferHoles sig = nub $ concatMap holesFor (expressions sig) ++ concatMap holesFor (backgroundExpressions sig) where
  holesFor = maybe [] (funTyHoles . dynTypeRep . snd) . unLit
  funTyHoles ty = case funTys ty of
    Just (argTy, resultTy) -> argTy : funTyHoles resultTy
    Nothing -> []
