{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Arrow ((&&&))
import Control.Concurrent.Classy
import Control.Monad (void)
import Control.Monad.ST (runST)
import Data.Maybe (listToMaybe)
import Data.Proxy (Proxy(..))
import Test.DejaFu.Conc

import Test.Spec.Concurrency
import Test.Spec.Expr (constant, stateVariable, variable)

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

exprsLS :: forall t. Exprs (LockStack (ConcST t) Int) (ConcST t) [Int]
exprsLS = Exprs
  { initialState = fromListLS
  , expressions =
    [ constant "pushLS"  (pushLS  :: Int -> LockStack (ConcST t) Int -> ConcST t ())
    , constant "popLS"   (popLS   :: LockStack (ConcST t) Int -> ConcST t (Maybe Int))
    , constant "peekLS"  (peekLS  :: LockStack (ConcST t) Int -> ConcST t (Maybe Int))
    , constant "swapLS"  (swapLS  :: LockStack (ConcST t) Int -> ConcST t Bool)
    , constant "dupLS"   (dupLS   :: LockStack (ConcST t) Int -> ConcST t Bool)
    , constant "overLS"  (overLS  :: LockStack (ConcST t) Int -> ConcST t Bool)
    , constant "rotLS"   (rotLS   :: LockStack (ConcST t) Int -> ConcST t Bool)
    ]
  , backgroundExpressions =
    [ constant "void"    (void    :: ConcST t Bool -> ConcST t ())
    , constant "void"    (void    :: ConcST t (Maybe Int) -> ConcST t ())
    , constant "|||"     ((|||)   :: ConcST t () -> ConcST t () -> ConcST t ())
    , variable "x"       (Proxy   :: Proxy Int)
    , stateVariable
    ]
  , observation = toListLS
  , eval = defaultEvaluate
  , setState = \(LockStack v) -> modifyMVar_ v . const . pure
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

exprsCAS :: forall t. Exprs (CASStack (ConcST t) Int) (ConcST t) [Int]
exprsCAS = Exprs
  { initialState = fromListCAS
  , expressions =
    [ constant "pushCAS"  (pushCAS  :: Int -> CASStack (ConcST t) Int -> ConcST t ())
    , constant "popCAS"   (popCAS   :: CASStack (ConcST t) Int -> ConcST t (Maybe Int))
    , constant "peekCAS"  (peekCAS  :: CASStack (ConcST t) Int -> ConcST t (Maybe Int))
    , constant "swapCAS"  (swapCAS  :: CASStack (ConcST t) Int -> ConcST t Bool)
    , constant "dupCAS"   (dupCAS   :: CASStack (ConcST t) Int -> ConcST t Bool)
    , constant "overCAS"  (overCAS  :: CASStack (ConcST t) Int -> ConcST t Bool)
    , constant "rotCAS"   (rotCAS   :: CASStack (ConcST t) Int -> ConcST t Bool)
    ]
  , backgroundExpressions =
    [ constant "void"     (void     :: ConcST t Bool -> ConcST t ())
    , constant "void"     (void     :: ConcST t (Maybe Int) -> ConcST t ())
    , constant "|||"      ((|||)    :: ConcST t () -> ConcST t () -> ConcST t ())
    , variable "x"        (Proxy    :: Proxy Int)
    , stateVariable
    ]
  , observation = toListCAS
  , eval = defaultEvaluate
  , setState = \(CASStack r) -> modifyCRefCAS_ r . const
  }

-------------------------------------------------------------------------------
-- Examples

example :: Int -> IO ()
example n = do
  let (obs1, obs2, obs3) = runST $ discover defaultListValues exprsLS exprsCAS n
  prettyPrint obs1
  putStrLn ""
  prettyPrint obs2
  putStrLn ""
  prettyPrint obs3

main :: IO ()
main = example 7
