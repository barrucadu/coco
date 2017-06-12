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

sigLS :: Sig (LockStack Concurrency Int) [Int] [Int]
sigLS = Sig
  { initialise  = fromListLS
  , expressions =
    [ lit "pushLS"  (pushLS  :: A -> LockStack Concurrency A -> Concurrency ())
    , lit "popLS"   (popLS   :: LockStack Concurrency A -> Concurrency (Maybe A))
    , lit "peekLS"  (peekLS  :: LockStack Concurrency A -> Concurrency (Maybe A))
    , lit "swapLS"  (swapLS  :: LockStack Concurrency A -> Concurrency Bool)
    , lit "dupLS"   (dupLS   :: LockStack Concurrency A -> Concurrency Bool)
    , lit "overLS"  (overLS  :: LockStack Concurrency A -> Concurrency Bool)
    , lit "rotLS"   (rotLS   :: LockStack Concurrency A -> Concurrency Bool)
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

sigCAS :: Sig (CASStack Concurrency Int) [Int] [Int]
sigCAS = Sig
  { initialise  = fromListCAS
  , expressions =
    [ lit "pushCAS"  (pushCAS  :: A -> CASStack Concurrency A -> Concurrency ())
    , lit "popCAS"   (popCAS   :: CASStack Concurrency A -> Concurrency (Maybe A))
    , lit "peekCAS"  (peekCAS  :: CASStack Concurrency A -> Concurrency (Maybe A))
    , lit "swapCAS"  (swapCAS  :: CASStack Concurrency A -> Concurrency Bool)
    , lit "dupCAS"   (dupCAS   :: CASStack Concurrency A -> Concurrency Bool)
    , lit "overCAS"  (overCAS  :: CASStack Concurrency A -> Concurrency Bool)
    , lit "rotCAS"   (rotCAS   :: CASStack Concurrency A -> Concurrency Bool)
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
