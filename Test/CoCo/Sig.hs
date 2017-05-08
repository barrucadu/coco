{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Test.CoCo.Sig
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ScopedTypeVariables
--
-- Expression signatures for property discovery.
module Test.CoCo.Sig where

import           Data.List       (nub)
import           Data.Maybe      (fromMaybe)
import           Data.Proxy      (Proxy(..))
import           Data.Typeable   (TypeRep, Typeable, typeRep)

import           Test.CoCo.Expr  (Schema, exprTypeRep, holeOf, instantiateTys,
                                  stateVar, unLit)
import           Test.CoCo.Monad (Concurrency)
import           Test.CoCo.Type  (dynTypeRep, funArgTys, unifyList)

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
  let sig' = monomorphiseState sig
      state = [ stateVar
              | stateVar `notElem` expressions           sig'
              , stateVar `notElem` backgroundExpressions sig'
              ]
      holes = [ h
              | h <- map holeOf (inferHoles sig')
              , h `notElem` expressions           sig'
              , h `notElem` backgroundExpressions sig'
              ]
  in sig' { backgroundExpressions = state ++ holes ++ backgroundExpressions sig' }

-- | Monomorphise polymorphic uses of the state type.
--
-- When writing type signatures, it's nice to be able to write
-- something like
--
-- > putMVar :: MVar Concurrency A -> A -> Concurrency ()
--
-- rather than
--
-- > putMVar :: MVar Concurrency Int -> Int -> Concurrency ()
--
-- The latter repeats the type in the @MVar@, and needs changing if
-- the state type is altered.  However, hole inference doesn't play
-- very nicely with polymorphism.  This function monomorphises all
-- function types which use a polymorphic variant of the state type,
-- and should be called before 'inferHoles'.
monomorphiseState :: forall s o x. Typeable s => Sig s o x -> Sig s o x
monomorphiseState sig = sig { expressions = map monomorphise (expressions sig)
                            , backgroundExpressions = map monomorphise (backgroundExpressions sig)
                            }
  where
    monomorphise e = fromMaybe e $ do
      (argTys, _) <- funArgTys (exprTypeRep e)
      assignments <- unifyList False stateTy argTys
      pure (instantiateTys assignments e)

    stateTy = typeRep (Proxy :: Proxy s)

-- | Infer necessary hole types in a signature.
inferHoles :: Sig s o x -> [TypeRep]
inferHoles sig = nub $ concatMap holesFor (expressions sig) ++ concatMap holesFor (backgroundExpressions sig) where
  holesFor = maybe [] (funTyHoles . dynTypeRep . snd) . unLit
  funTyHoles = maybe [] fst . funArgTys
