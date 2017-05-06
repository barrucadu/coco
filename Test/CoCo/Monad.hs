{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Test.CoCo.Monad
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GeneralizedNewtypeDeriving, TypeFamilies, UndecidableInstances
--
-- The concurrency monad.
module Test.CoCo.Monad
  ( Concurrency
  , subconcurrency
  , runSCT
  , runSCT'
  ) where

import Control.Monad.Conc.Class (MonadConc(..))
import Control.Monad.Catch (MonadCatch, MonadMask, MonadThrow)
import qualified Test.DejaFu as D
import qualified Test.DejaFu.Conc as D
import qualified Test.DejaFu.SCT as D
import Data.Proxy (Proxy(..))
import System.IO.Unsafe (unsafePerformIO)
import Control.DeepSeq (NFData)

-- | The concurrency monad.
newtype Concurrency a = Concurrency { toConcIO :: D.ConcIO a }
  deriving (Functor, Applicative, Monad, MonadThrow, MonadCatch, MonadMask)

instance MonadConc Concurrency where
  type MVar     Concurrency = MVar     D.ConcIO
  type CRef     Concurrency = CRef     D.ConcIO
  type Ticket   Concurrency = Ticket   D.ConcIO
  type STM      Concurrency = STM      D.ConcIO
  type ThreadId Concurrency = ThreadId D.ConcIO

  fork     = Concurrency . fork     . toConcIO
  forkOn i = Concurrency . forkOn i . toConcIO

  forkWithUnmask        ca = Concurrency $ forkWithUnmask        (\unmask -> toConcIO $ ca $ \ma -> Concurrency (unmask (toConcIO ma)))
  forkWithUnmaskN   n   ca = Concurrency $ forkWithUnmaskN   n   (\unmask -> toConcIO $ ca $ \ma -> Concurrency (unmask (toConcIO ma)))
  forkOnWithUnmask    i ca = Concurrency $ forkOnWithUnmask    i (\unmask -> toConcIO $ ca $ \ma -> Concurrency (unmask (toConcIO ma)))
  forkOnWithUnmaskN n i ca = Concurrency $ forkOnWithUnmaskN n i (\unmask -> toConcIO $ ca $ \ma -> Concurrency (unmask (toConcIO ma)))

  getNumCapabilities = Concurrency getNumCapabilities
  setNumCapabilities = Concurrency . setNumCapabilities
  myThreadId         = Concurrency myThreadId
  yield              = Concurrency yield
  threadDelay        = Concurrency . threadDelay
  throwTo t          = Concurrency . throwTo t
  newEmptyMVar       = Concurrency newEmptyMVar
  newEmptyMVarN      = Concurrency . newEmptyMVarN
  readMVar           = Concurrency . readMVar
  tryReadMVar        = Concurrency . tryReadMVar
  putMVar v          = Concurrency . putMVar v
  tryPutMVar v       = Concurrency . tryPutMVar v
  takeMVar           = Concurrency . takeMVar
  tryTakeMVar        = Concurrency . tryTakeMVar
  newCRef            = Concurrency . newCRef
  newCRefN n         = Concurrency . newCRefN n
  readCRef           = Concurrency . readCRef
  atomicModifyCRef r = Concurrency . atomicModifyCRef r
  writeCRef r        = Concurrency . writeCRef r
  atomicWriteCRef r  = Concurrency . atomicWriteCRef r
  readForCAS         = Concurrency . readForCAS
  peekTicket' _      = peekTicket' (Proxy :: Proxy Concurrency)
  casCRef r t        = Concurrency . casCRef r t
  modifyCRefCAS r    = Concurrency . modifyCRefCAS r
  atomically         = Concurrency . atomically
  readTVarConc       = Concurrency . readTVarConc

-- | Explore possible executions of a concurrent program.
runSCT :: Concurrency a -> [(Either D.Failure a, D.Trace)]
runSCT (Concurrency ca) =
  -- this is safe as Concurrency has no MonadIO instance
  unsafePerformIO (D.runSCT D.defaultWay D.defaultMemType ca)

-- | A strict variant of 'runSCT'.
--
-- Demanding the result of this will force it to normal form, which
-- may be more efficient in some situations.
runSCT' :: NFData a => Concurrency a -> [(Either D.Failure a, D.Trace)]
runSCT' (Concurrency ca) =
  -- this is safe as Concurrency has no MonadIO instance
  unsafePerformIO (D.runSCT' D.defaultWay D.defaultMemType ca)

-- | Run a concurrent computation and return its result.
--
-- This can only be called in the main thread, when no other threads
-- exist. Calls to subconcurrency cannot be nested. Violating either
-- of these conditions will result in the computation failing with
-- @IllegalSubconcurrency@.
subconcurrency :: Concurrency a -> Concurrency (Either D.Failure a)
subconcurrency (Concurrency ca) =
  Concurrency (D.subconcurrency ca)
