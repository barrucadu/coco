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

import Test.CoCo.Expr (Schema)

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
  , observation :: s -> m o
  -- ^ The observation to make.
  , backToSeed :: s -> m x
  -- ^ Convert the state back to the seed (used to determine if a term
  -- is boring).
  , setState :: s -> x -> m ()
  -- ^ Set the state value. This doesn't need to be atomic, or even
  -- guaranteed to work, its purpose is to cause interference when
  -- evaluating other terms.
  }
