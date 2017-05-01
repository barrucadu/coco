{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Arrow ((&&&))
import Control.Concurrent.Classy
import Control.Monad.ST (runST)
import Data.Maybe (listToMaybe)
import Data.Proxy (Proxy(..))
import Test.DejaFu.Conc

import Test.CoCo.Concurrency
import Test.CoCo.Expr

-------------------------------------------------------------------------------
-- Lock-based stack

newtype LockStack m a = LockStack (MVar m [a])

pushLS :: MonadConc m => a -> LockStack m a -> m ()
pushLS a (LockStack v) = modifyMVar_ v $ pure . (a:)

popLS :: MonadConc m => LockStack m a -> m (Maybe a)
popLS (LockStack v) = modifyMVar v $ pure . (drop 1 &&& listToMaybe)

peekLS :: MonadConc m => LockStack m a -> m (Maybe a)
peekLS (LockStack v) = listToMaybe <$> readMVar v

swapLS :: MonadConc m => LockStack m a -> m Bool
swapLS (LockStack v) = modifyMVar v $ pure . go where
  go (a:b:xs) = (b:a:xs, True)
  go xs = (xs, False)

dupLS :: MonadConc m => LockStack m a -> m Bool
dupLS (LockStack v) = modifyMVar v $ pure . go where
  go (a:xs) = (a:a:xs, True)
  go xs = (xs, False)

overLS :: MonadConc m => LockStack m a -> m Bool
overLS (LockStack v) = modifyMVar v $ pure . go where
  go (a:b:xs) = (b:a:b:xs, True)
  go xs = (xs, False)

rotLS :: MonadConc m => LockStack m a -> m Bool
rotLS (LockStack v) = modifyMVar v $ pure . go where
  go (a:b:c:xs) = (c:a:b:xs, True)
  go xs = (xs, False)

fromListLS :: MonadConc m => [a] -> m (LockStack m a)
fromListLS as = LockStack <$> newMVar as

toListLS :: MonadConc m => LockStack m a -> m [a]
toListLS (LockStack v) = readMVar v

exprsLS :: forall t. Exprs (LockStack (ConcST t) Int) (ConcST t) [Int] [Int]
exprsLS = Exprs
  { initialState = fromListLS
  , expressions =
    [ lit "pushLS"  (pushLS  :: Int -> LockStack (ConcST t) Int -> ConcST t ())
    , lit "popLS"   (popLS   :: LockStack (ConcST t) Int -> ConcST t (Maybe Int))
    , lit "peekLS"  (peekLS  :: LockStack (ConcST t) Int -> ConcST t (Maybe Int))
    , lit "swapLS"  (swapLS  :: LockStack (ConcST t) Int -> ConcST t Bool)
    , lit "dupLS"   (dupLS   :: LockStack (ConcST t) Int -> ConcST t Bool)
    , lit "overLS"  (overLS  :: LockStack (ConcST t) Int -> ConcST t Bool)
    , lit "rotLS"   (rotLS   :: LockStack (ConcST t) Int -> ConcST t Bool)
    ]
  , backgroundExpressions =
    [ lit "whenJust" ((\f s -> maybe (pure ()) (`f` s)) :: (Int -> LockStack (ConcST t) Int -> ConcST t ())
                                                        -> LockStack (ConcST t) Int
                                                        -> Maybe Int
                                                        -> ConcST t ())
    , commLit "|||" ((|||) :: ConcST t Ignore -> ConcST t Ignore -> ConcST t ())
    , hole (Proxy :: Proxy (Maybe Int))
    , stateVar
    ]
  , observation = toListLS
  , backToSeed = toListLS
  , setState = \(LockStack v) -> modifyMVar_ v . const . pure
  , eval   = defaultEvaluate
  }

-------------------------------------------------------------------------------
-- CAS-based stack

newtype CASStack m a = CASStack (CRef m [a])

pushCAS :: MonadConc m => a -> CASStack m a -> m ()
pushCAS a (CASStack r) = modifyCRefCAS_ r (a:)

popCAS :: MonadConc m => CASStack m a -> m (Maybe a)
popCAS (CASStack r) = modifyCRefCAS r (drop 1 &&& listToMaybe)

peekCAS :: MonadConc m => CASStack m a -> m (Maybe a)
peekCAS (CASStack r) = listToMaybe <$> readCRef r

swapCAS :: MonadConc m => CASStack m a -> m Bool
swapCAS (CASStack r) = modifyCRefCAS r go where
  go (a:b:xs) = (b:a:xs, True)
  go xs = (xs, False)

dupCAS :: MonadConc m => CASStack m a -> m Bool
dupCAS (CASStack r) = modifyCRefCAS r go where
  go (a:xs) = (a:a:xs, True)
  go xs = (xs, False)

overCAS :: MonadConc m => CASStack m a -> m Bool
overCAS (CASStack r) = modifyCRefCAS r go where
  go (a:b:xs) = (b:a:b:xs, True)
  go xs = (xs, False)

rotCAS :: MonadConc m => CASStack m a -> m Bool
rotCAS (CASStack r) = modifyCRefCAS r go where
  go (a:b:c:xs) = (c:a:b:xs, True)
  go xs = (xs, False)

fromListCAS :: MonadConc m => [a] -> m (CASStack m a)
fromListCAS as = CASStack <$> newCRef as

toListCAS :: MonadConc m => CASStack m a -> m [a]
toListCAS (CASStack r) = readCRef r

exprsCAS :: forall t. Exprs (CASStack (ConcST t) Int) (ConcST t) [Int] [Int]
exprsCAS = Exprs
  { initialState = fromListCAS
  , expressions =
    [ lit "pushCAS"  (pushCAS  :: Int -> CASStack (ConcST t) Int -> ConcST t ())
    , lit "popCAS"   (popCAS   :: CASStack (ConcST t) Int -> ConcST t (Maybe Int))
    , lit "peekCAS"  (peekCAS  :: CASStack (ConcST t) Int -> ConcST t (Maybe Int))
    , lit "swapCAS"  (swapCAS  :: CASStack (ConcST t) Int -> ConcST t Bool)
    , lit "dupCAS"   (dupCAS   :: CASStack (ConcST t) Int -> ConcST t Bool)
    , lit "overCAS"  (overCAS  :: CASStack (ConcST t) Int -> ConcST t Bool)
    , lit "rotCAS"   (rotCAS   :: CASStack (ConcST t) Int -> ConcST t Bool)
    ]
  , backgroundExpressions =
    [ lit "whenJust" ((\f s -> maybe (pure ()) (`f` s)) :: (Int -> CASStack (ConcST t) Int -> ConcST t ())
                                                        -> CASStack (ConcST t) Int
                                                        -> Maybe Int
                                                        -> ConcST t ())
    , commLit "|||" ((|||) :: ConcST t Ignore -> ConcST t Ignore -> ConcST t ())
    , hole (Proxy :: Proxy (Maybe Int))
    , stateVar
    ]
  , observation = toListCAS
  , backToSeed = toListCAS
  , setState = \(CASStack r) -> modifyCRefCAS_ r . const
  , eval   = defaultEvaluate
  }

-------------------------------------------------------------------------------
-- Examples

seedPreds :: [(String, [a] -> Bool)]
seedPreds = []

example :: Int -> IO ()
example n = do
  let (obs1, obs2, obs3) = runST $ discover defaultTypeInfos seedPreds exprsLS exprsCAS n
  prettyPrint defaultTypeInfos obs1
  putStrLn ""
  prettyPrint defaultTypeInfos obs2
  putStrLn ""
  prettyPrint defaultTypeInfos obs3

main :: IO ()
main = example 7
