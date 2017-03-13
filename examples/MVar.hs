{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Concurrent.Classy
import Control.Monad
import Control.Monad.ST
import Data.Proxy
import Test.DejaFu.Conc

import Test.Spec.Concurrency
import Test.Spec.Expr

exprs :: forall t. Exprs (MVar (ConcST t) Int) (ConcST t) (Maybe Int)
exprs = Exprs
  { initialState = maybe newEmptyMVar newMVar
  , expressions =
    [ constant "putMVar"  (putMVar  :: MVar (ConcST t) Int -> Int -> ConcST t ())
    , constant "takeMVar" (takeMVar :: MVar (ConcST t) Int -> ConcST t Int)
    , constant "readMVar" (readMVar :: MVar (ConcST t) Int -> ConcST t Int)
    ]
  , backgroundExpressions =
    [ commutativeConstant "|||" ((|||) :: ConcST t Ignore -> ConcST t Ignore -> ConcST t ())
    , variable "x" (Proxy :: Proxy Int)
    , stateVariable
    ]
  , observation = tryTakeMVar
  , eval = defaultEvaluate
  , setState = \v mi -> tryTakeMVar v >> maybe (pure ()) (void . tryPutMVar v) mi
  }

-- | For using in GHCi
example :: Int -> IO ()
example n = prettyPrint $ runST $ discoverSingle defaultListValues exprs n

main :: IO ()
main = example 7
