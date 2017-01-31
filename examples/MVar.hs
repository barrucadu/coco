{-# LANGUAGE ScopedTypeVariables #-}

import Control.Concurrent.Classy
import Control.Monad
import Control.Monad.ST
import Data.Proxy
import Test.DejaFu.Conc

import Test.Spec.Concurrency
import Test.Spec.Expr

exprs :: forall t. Exprs (MVar (ConcST t) Int) (ConcST t) (Maybe Int) (Maybe Int)
exprs = Exprs
  { initialState = maybe newEmptyMVar newMVar
  , expressions = [ constant "putMVar"  (putMVar  :: MVar (ConcST t) Int -> Int -> ConcST t ())
                  , constant "takeMVar" (takeMVar :: MVar (ConcST t) Int -> ConcST t Int)
                  , constant "readMVar" (readMVar :: MVar (ConcST t) Int -> ConcST t Int)
                  , constant "void"     (void     :: ConcST t Int -> ConcST t ())
                  , constant "|||"      ((|||)    :: ConcST t () -> ConcST t () -> ConcST t ())
                  , variable "x"        (Proxy    :: Proxy Int)
                  , stateVariable
                  ]
  , observation = constant "tryTakeMVar" (tryTakeMVar :: MVar (ConcST t) Int -> ConcST t (Maybe Int))
  , eval = defaultEvaluate
  }

-- | For using in GHCi
example :: Int -> IO ()
example n = mapM_ print $ runST $ discoverSingle defaultListValues exprs n

main :: IO ()
main = example 10
