-- |
-- Module      : Test.CoCo.Discover
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : MonoLocalBinds, ScopedTypeVariables, TupleSections
--
-- Discover observational equalities and refinements between
-- concurrent functions.
module Test.CoCo
  ( -- * Property discovery
    L.Observation(..)
  , D.discover
  , D.discoverSingle
    -- * Signatures
  , M.Concurrency
  , S.Sig(..)
  , T.A
  , T.B
  , T.C
  , T.D
  , E.lit
  , E.commLit
  , E.showLit
    -- * Types
  , T.TypeInfo(..)
  , T.defaultTypeInfos
  , T.makeTypeInfo
  , T.toDyn
    -- * Miscellaneous
  , (|||)
  , PPROpts(..)
  , DejaFuCompat(..)
  , defaultPPROpts
  , prettyPrint
  , S.cocoToDejaFu
  ) where

import           Control.Monad            (void)
import           Control.Monad.Conc.Class (readMVar, spawn)
import           Data.List                (sortOn)
import           Data.Maybe               (isJust)
import           Data.Typeable            (TypeRep, Typeable)

import qualified Test.CoCo.Discover       as D
import qualified Test.CoCo.Expr           as E
import qualified Test.CoCo.Logic          as L
import qualified Test.CoCo.Monad          as M
import qualified Test.CoCo.Sig            as S
import qualified Test.CoCo.Type           as T
import qualified Test.CoCo.TypeInfo       as T
import           Test.CoCo.Util           (ordNub)

-- | Concurrent composition. Waits for both component computations to
-- finish.
(|||) :: M.Concurrency a -> M.Concurrency b -> M.Concurrency ()
a ||| b = do
  j <- spawn a
  void b
  void (readMVar j)

-- | What sort of dejafu-compatible output to produce.
data DejaFuCompat
  = Plain
  -- ^ Use @check@ from Test.DejaFu.Refinement.
  | HUnit
  -- ^ Use @testProperty@ from Test.HUnit.DejaFu.
  | Tasty
  -- ^ Use @testProperty@ from Test.HUnit.Tasty.
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | Options for the pretty-printer
data PPROpts = PPROpts
  { pprTypeInfos :: [(TypeRep, T.TypeInfo)]
  -- ^ Type infos, used to give names to variables.
  , pprDejaFu    :: Maybe DejaFuCompat
  -- ^ Whether to produce dejafu-compatible output.
  }

-- | Default pretty-printer options.
defaultPPROpts :: PPROpts
defaultPPROpts = PPROpts
  { pprTypeInfos = T.defaultTypeInfos
  , pprDejaFu    = Nothing
  }

-- | Pretty-print a list of observations.
prettyPrint :: PPROpts -> [L.Observation] -> IO ()
prettyPrint opts obss0 = mapM_ (putStrLn . ppr) (sortOn cmp obss) where
  obss = map go obss0 where
    go (L.Equiv   lr e1 e2) =
      (Nothing, pp e1, "===", pp e2, map fst . ordNub $ E.environment e1 ++ E.environment e2, lr)
    go (L.Refines lr e1 e2) =
      (Nothing, pp e1, "->-", pp e2, map fst . ordNub $ E.environment e1 ++ E.environment e2, lr)
    go (L.Implied p obs) =
      let (Nothing, e1p, t, e2p, env, lr) = go obs in (Just p, e1p, t, e2p, env, lr)

  cmp (p, e1p, _, e2p, _, _) =
    (maybe 0 length p, p, length e1p, e1p, length e2p, e2p)

  ppr (p, e1p, t, e2p, env, lr) = case pprDejaFu opts of
    Just style ->
      let how = case style of
            Plain -> "check"
            HUnit -> "testProperty \"name\""
            Tasty -> "testProperty \"name\""
          lambda = if null env then "" else '\\' : unwords env ++ " -> "
          prefix = maybe "" (++ " ==> ") p
          (sig1, sig2) = case lr of
            L.LL -> ("sigL", "sigL")
            L.RR -> ("sigR", "sigR")
            L.LR -> ("sigL", "sigR")
            L.RL -> ("sigR", "sigL")
      in how ++ " $ " ++ lambda ++ prefix ++ sig1 ++ " (\\h0 -> " ++ e1p ++ ") " ++ t ++ " " ++ sig2 ++ " (\\h0 -> " ++ e2p ++ ")"
    Nothing ->
      let off = replicate (maxlen p - length e1p) ' '
          prefix = maybe "" (++ "  ==>  ") p
      in prefix ++ off ++ e1p ++ "  " ++ t ++ "  " ++ e2p

  maxlen p0 = maximum (map (\(p, e1p, _, _, _, _) -> if p == p0 then length e1p else 0) obss)

  nf = T.getVariableBaseName (pprTypeInfos opts)

  pp :: Typeable s => E.Expr s h -> String
  pp = E.pp nf (isJust $ pprDejaFu opts)
