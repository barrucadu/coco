module Main where

import           Control.Concurrent.Classy.MVar
import           Control.Monad.Catch            (mask_, onException,
                                                 uninterruptibleMask_)
import           Control.Monad.Conc.Class       (MonadConc)
import           Data.Maybe

import           Test.CoCo

sig :: Sig (QSemN Concurrency) Int Int
sig = Sig
  { initialise  = newQSemN . abs
  , expressions =
    [ lit "wait" (waitQSemN :: QSemN Concurrency -> Int -> Concurrency ())
    , lit "signal" (signalQSemN :: QSemN Concurrency -> Int -> Concurrency ())
    ]
  , backgroundExpressions =
    [ commLit "|||" ((|||) :: Concurrency A -> Concurrency B -> Concurrency ())
    , lit "remaining" (remainingQSemN :: QSemN Concurrency -> Concurrency Int)
    , commLit "+" ((+) :: Int -> Int -> Int)
    , lit "-" ((-) :: Int -> Int -> Int)
    , lit "0" (0 :: Int)
    , lit "1" (1 :: Int)
    ]
  , observe    = \q _ -> remainingQSemN q
  , interfere  = \q n -> let i = abs (n `div` 2) in waitQSemN q i >> signalQSemN q i
  , backToSeed = \q _ -> remainingQSemN q
  }

example :: Int -> IO ()
example = prettyPrint defaultTypeInfos . discoverSingle defaultTypeInfos [] sig

main :: IO ()
main = example 7

-------------------------------------------------------------------------------
-- Implementation of QSemN

newtype QSemN m = QSemN (MVar m (Int, [(Int, MVar m ())], [(Int, MVar m ())]))

newQSemN :: MonadConc m => Int -> m (QSemN m)
newQSemN initial
  | initial < 0 = fail "newQSemN: Initial quantity must be non-negative"
  | otherwise   = QSemN <$> newMVar (initial, [], [])

remainingQSemN :: MonadConc m => QSemN m -> m Int
remainingQSemN (QSemN m) = (\(quantity, _, _) -> quantity) <$> readMVar m

waitQSemN :: MonadConc m => QSemN m -> Int -> m ()
waitQSemN (QSemN m) sz = mask_ $ do
  (quantity, b1, b2) <- takeMVar m
  let remaining = quantity - sz
  if remaining < 0
    then do
      b <- newEmptyMVar
      putMVar m (quantity, b1, (sz,b):b2)
      wait b
    else
      putMVar m (remaining, b1, b2)

  where
    wait b = takeMVar b `onException` uninterruptibleMask_ (do
      (quantity, b1, b2) <- takeMVar m
      r  <- tryTakeMVar b
      r' <- if isJust r
           then signal sz (quantity, b1, b2)
           else putMVar b () >> pure (quantity, b1, b2)
      putMVar m r')

signalQSemN :: MonadConc m => QSemN m -> Int -> m ()
signalQSemN (QSemN m) sz = uninterruptibleMask_ $ do
  r  <- takeMVar m
  r' <- signal sz r
  putMVar m r'

signal :: MonadConc m
  => Int
  -> (Int, [(Int,MVar m ())], [(Int,MVar m ())])
  -> m (Int, [(Int,MVar m ())], [(Int,MVar m ())])
signal sz0 (i,a1,a2) = loop (sz0 + i) a1 a2 where
  loop 0 bs b2 = pure (0,  bs, b2)
  loop sz [] [] = pure (sz, [], [])
  loop sz [] b2 = loop sz (reverse b2) []
  loop sz ((j,b):bs) b2
    | j > sz = do
      r <- isEmptyMVar b
      if r then pure (sz, (j,b):bs, b2)
           else loop sz bs b2
    | otherwise = do
      r <- tryPutMVar b ()
      if r then loop (sz-j) bs b2
           else loop sz bs b2

