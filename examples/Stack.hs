{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Arrow ((&&&))
import Control.Concurrent.Classy
import Control.Monad.ST (runST)
import Data.Maybe (listToMaybe)
import Data.Proxy (Proxy(..))
import Test.DejaFu.Conc

import Test.Spec.Concurrency
import Test.Spec.Expr

-------------------------------------------------------------------------------
-- Lock-based stack

newtype LockStack m a = LockStack (MVar m [a])

pushLS :: MonadConc m => a -> LockStack m a -> m ()
pushLS a (LockStack v) = modifyMVar_ v $ pure . (a:)

-- | Incorrect function to push two values atomically.
push2LS :: MonadConc m => a -> a -> LockStack m a -> m ()
push2LS _ a2 (LockStack v) = modifyMVar_ v $ pure . ([a2,a2]++)

popLS :: MonadConc m => LockStack m a -> m (Maybe a)
popLS (LockStack v) = modifyMVar v $ pure . (drop 1 &&& listToMaybe)

peekLS :: MonadConc m => LockStack m a -> m (Maybe a)
peekLS (LockStack v) = listToMaybe <$> readMVar v

fromListLS :: MonadConc m => [a] -> m (LockStack m a)
fromListLS as = LockStack <$> newMVar as

toListLS :: MonadConc m => LockStack m a -> m [a]
toListLS (LockStack v) = readMVar v

exprsLS :: forall t. Exprs (LockStack (ConcST t) Int) (ConcST t) [Int]
exprsLS = Exprs
  { initialState = fromListLS
  , expressions =
    [ lit "pushLS"  (pushLS  :: Int -> LockStack (ConcST t) Int -> ConcST t ())
    , lit "push2LS" (push2LS :: Int -> Int -> LockStack (ConcST t) Int -> ConcST t ())
    , lit "popLS"   (popLS   :: LockStack (ConcST t) Int -> ConcST t (Maybe Int))
    , lit "peekLS"  (peekLS  :: LockStack (ConcST t) Int -> ConcST t (Maybe Int))
    ]
  , backgroundExpressions =
    [ lit "whenJust" ((\f s -> maybe (pure ()) (`f` s)) :: (Int -> LockStack (ConcST t) Int -> ConcST t ())
                                                        -> LockStack (ConcST t) Int
                                                        -> Maybe Int
                                                        -> ConcST t ())
    , commLit "|||" ((|||) :: ConcST t Ignore -> ConcST t Ignore -> ConcST t ())
    , hole (Proxy :: Proxy Int)
    , hole (Proxy :: Proxy (Maybe Int))
    , stateVar
    ]
  , observation = toListLS
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

fromListCAS :: MonadConc m => [a] -> m (CASStack m a)
fromListCAS as = CASStack <$> newCRef as

toListCAS :: MonadConc m => CASStack m a -> m [a]
toListCAS (CASStack r) = readCRef r

exprsCAS :: forall t. Exprs (CASStack (ConcST t) Int) (ConcST t) [Int]
exprsCAS = Exprs
  { initialState = fromListCAS
  , expressions =
    [ lit "pushCAS"  (pushCAS  :: Int -> CASStack (ConcST t) Int -> ConcST t ())
    , lit "popCAS"   (popCAS   :: CASStack (ConcST t) Int -> ConcST t (Maybe Int))
    , lit "peekCAS"  (peekCAS  :: CASStack (ConcST t) Int -> ConcST t (Maybe Int))
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
  , setState = \(CASStack r) -> modifyCRefCAS_ r . const
  , eval   = defaultEvaluate
  }

-------------------------------------------------------------------------------
-- Examples

example :: Int -> IO ()
example n = do
  let (obs1, obs2, obs3) = runST $ discover defaultTypeInfos exprsLS exprsCAS n
  prettyPrint defaultTypeInfos obs1
  putStrLn ""
  prettyPrint defaultTypeInfos obs2
  putStrLn ""
  prettyPrint defaultTypeInfos obs3

main :: IO ()
main = example 7
