{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Concurrent.Classy
import Control.Monad

import Test.CoCo

sig :: forall t. Sig (MVar (ConcST t) Int) (ConcST t) (Maybe Int) (Maybe Int)
sig = Sig
  { initialState = maybe newEmptyMVar newMVar
  , expressions =
    [ lit "putMVar"  (putMVar  :: MVar (ConcST t) Int -> Int -> ConcST t ())
    , lit "takeMVar" (takeMVar :: MVar (ConcST t) Int -> ConcST t Int)
    , lit "readMVar" (readMVar :: MVar (ConcST t) Int -> ConcST t Int)
    ]
  , backgroundExpressions =
    [ commLit "|||" ((|||) :: ConcST t Ignore -> ConcST t Ignore -> ConcST t ()) ]
  , observation = const . tryTakeMVar
  , backToSeed = const . tryTakeMVar
  , setState = \v mi -> tryTakeMVar v >> maybe (pure ()) (void . tryPutMVar v) mi
  }

seedPreds :: [(String, Maybe a -> Bool)]
seedPreds = []

-- | For using in GHCi
example :: Int -> IO ()
example n = prettyPrint defaultTypeInfos $ runST $ discoverSingle defaultTypeInfos seedPreds sig n

main :: IO ()
main = example 7
