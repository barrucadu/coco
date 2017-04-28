{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Concurrent.Classy
import Control.Monad
import Control.Monad.ST
import Data.Proxy
import Test.DejaFu.Conc

import Test.CoCo.Concurrency
import Test.CoCo.Expr

exprs :: forall t. Exprs (MVar (ConcST t) Int) (ConcST t) (Maybe Int)
exprs = Exprs
  { initialState = maybe newEmptyMVar newMVar
  , expressions =
    [ lit "putMVar"  (putMVar  :: MVar (ConcST t) Int -> Int -> ConcST t ())
    , lit "takeMVar" (takeMVar :: MVar (ConcST t) Int -> ConcST t Int)
    , lit "readMVar" (readMVar :: MVar (ConcST t) Int -> ConcST t Int)
    ]
  , backgroundExpressions =
    [ commLit "|||" ((|||) :: ConcST t Ignore -> ConcST t Ignore -> ConcST t ())
    , hole (Proxy :: Proxy Int)
    , stateVar
    ]
  , observation = tryTakeMVar
  , setState = \v mi -> tryTakeMVar v >> maybe (pure ()) (void . tryPutMVar v) mi
  , eval   = defaultEvaluate
  }

seedPreds :: [(String, Maybe a -> Bool)]
seedPreds = []

-- | For using in GHCi
example :: Int -> IO ()
example n = prettyPrint defaultTypeInfos $ runST $ discoverSingle defaultTypeInfos seedPreds exprs n

main :: IO ()
main = example 7
