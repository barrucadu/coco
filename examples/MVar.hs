module Main where

import           Control.Concurrent.Classy
import           Control.Monad

import           Test.CoCo

import           Util

sig :: Sig (MVar Concurrency Int) (Maybe Int) (Maybe Int)
sig = Sig
  { initialise  = maybe newEmptyMVar newMVar
  , expressions =
    [ lit "putMVar"  (putMVar  :: MVar Concurrency A -> A -> Concurrency ())
    , lit "takeMVar" (takeMVar :: MVar Concurrency A -> Concurrency A)
    , lit "readMVar" (readMVar :: MVar Concurrency A -> Concurrency A)
    ]
  , backgroundExpressions =
    [ commLit "|||" ((|||) :: Concurrency A -> Concurrency B -> Concurrency ()) ]
  , observe    = const . tryTakeMVar
  , interfere  = \v mi -> tryTakeMVar v >> maybe (pure ()) (void . tryPutMVar v) mi
  , backToSeed = const . tryTakeMVar
  }

seedPreds :: [(String, Maybe a -> Bool)]
seedPreds = []

-- | For using in GHCi
example :: Int -> IO ()
example = printOutput . discoverSingle defaultTypeInfos seedPreds sig

main :: IO ()
main = example 7
