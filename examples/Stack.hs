module Main where

import           Control.Arrow             ((&&&))
import           Control.Concurrent.Classy
import           Data.Maybe                (listToMaybe)

import           Test.CoCo

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

sigLS :: Sig (LockStack Concurrency Int) [Int] [Int]
sigLS = Sig
  { initialise  = fromListLS
  , expressions =
    [ lit "pushLS"  (pushLS  :: A -> LockStack Concurrency A -> Concurrency ())
    , lit "push2LS" (push2LS :: A -> A -> LockStack Concurrency A -> Concurrency ())
    , lit "popLS"   (popLS   :: LockStack Concurrency A -> Concurrency (Maybe A))
    , lit "peekLS"  (peekLS  :: LockStack Concurrency A -> Concurrency (Maybe A))
    ]
  , backgroundExpressions =
    [ lit "whenJust" ((\f s -> maybe (pure ()) (`f` s)) :: (A -> LockStack Concurrency A -> Concurrency ())
                                                        -> LockStack Concurrency A
                                                        -> Maybe A
                                                        -> Concurrency ())
    , commLit "|||" ((|||) :: Concurrency A -> Concurrency B -> Concurrency ())
    ]
  , observe    = const . toListLS
  , interfere  = \(LockStack v) -> modifyMVar_ v . const . pure
  , backToSeed = const . toListLS
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

sigCAS :: Sig (CASStack Concurrency Int) [Int] [Int]
sigCAS = Sig
  { initialise  = fromListCAS
  , expressions =
    [ lit "pushCAS"  (pushCAS  :: A -> CASStack Concurrency A -> Concurrency ())
    , lit "popCAS"   (popCAS   :: CASStack Concurrency A -> Concurrency (Maybe A))
    , lit "peekCAS"  (peekCAS  :: CASStack Concurrency A -> Concurrency (Maybe A))
    ]
  , backgroundExpressions =
    [ lit "whenJust" ((\f s -> maybe (pure ()) (`f` s)) :: (A -> CASStack Concurrency A -> Concurrency ())
                                                        -> CASStack Concurrency A
                                                        -> Maybe A
                                                        -> Concurrency ())
    , commLit "|||" ((|||) :: Concurrency A -> Concurrency B -> Concurrency ())
    ]
  , observe    = const . toListCAS
  , interfere  = \(CASStack r) -> modifyCRefCAS_ r . const
  , backToSeed = const . toListCAS
  }

-------------------------------------------------------------------------------
-- Examples

seedPreds :: [(String, [a] -> Bool)]
seedPreds = []

example :: Int -> IO ()
example n = do
  let (obs1, obs2, obs3) = discover defaultTypeInfos seedPreds sigLS sigCAS n
  prettyPrint defaultPPROpts obs1
  putStrLn ""
  prettyPrint defaultPPROpts obs2
  putStrLn ""
  prettyPrint defaultPPROpts obs3

main :: IO ()
main = example 7
