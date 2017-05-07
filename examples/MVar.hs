module Main where

import           Control.Concurrent.Classy
import           Control.Monad

import           Test.CoCo

sig :: Sig (MVar Concurrency Int) (Maybe Int) (Maybe Int)
sig = Sig
  { initialState = maybe newEmptyMVar newMVar
  , expressions =
    [ lit "putMVar"  (putMVar  :: MVar Concurrency Int -> Int -> Concurrency ())
    , lit "takeMVar" (takeMVar :: MVar Concurrency Int -> Concurrency Int)
    , lit "readMVar" (readMVar :: MVar Concurrency Int -> Concurrency Int)
    ]
  , backgroundExpressions =
    [ commLit "|||" ((|||) :: Concurrency Ignore -> Concurrency Ignore -> Concurrency ()) ]
  , observation = const . tryTakeMVar
  , backToSeed = const . tryTakeMVar
  , setState = \v mi -> tryTakeMVar v >> maybe (pure ()) (void . tryPutMVar v) mi
  }

seedPreds :: [(String, Maybe a -> Bool)]
seedPreds = []

-- | For using in GHCi
example :: Int -> IO ()
example = prettyPrint defaultTypeInfos . discoverSingle defaultTypeInfos seedPreds sig

main :: IO ()
main = example 7
