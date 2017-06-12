{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Test.CoCo
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : RecordWildCards
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
import           Data.Function            (on)
import           Data.List                (sort)
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

data PPRProp = PPRProp
  { prettyLExpr :: String
  , prettyRExpr :: String
  , prettyOp    :: String
  , prettyPred  :: Maybe String
  , prettyLSig  :: String
  , prettyRSig  :: String
  , prettyArgs  :: [String]
  } deriving Eq

instance Ord PPRProp where
  compare = compare `on` cmp where
    cmp PPRProp{..} =
      ( maybe 0 length prettyPred
      , prettyPred
      , length prettyLExpr
      , prettyLExpr
      , length prettyRExpr
      , prettyRExpr
      )

-- | Pretty-print a list of observations.
prettyPrint :: PPROpts -> [L.Observation] -> IO ()
prettyPrint opts obss0 = mapM_ (putStrLn . ppr) (sort obss) where
  obss = map go obss0 where
    go (L.Equiv   lr e1 e2) = go' "===" "===" lr e1 e2
    go (L.Refines lr e1 e2) = go' "->-" "-<-" lr e1 e2
    go (L.Implied p obs)    = (go obs) { prettyPred = Just p }

    go' t1 t2 lr e1 e2 = PPRProp
      { prettyPred  = Nothing
      , prettyLExpr = if lr == L.RL then pp e2  else pp e1
      , prettyRExpr = if lr == L.RL then pp e1  else pp e2
      , prettyOp    = if lr == L.RL then t2     else t1
      , prettyLSig  = if lr == L.RR then "sigR" else "sigL"
      , prettyRSig  = if lr == L.LL then "sigL" else "sigR"
      , prettyArgs  = map fst . ordNub $ E.environment e1 ++ E.environment e2
      }

  ppr PPRProp{..} = case pprDejaFu opts of
    Just style ->
      let how = case style of
            Plain -> "check"
            HUnit -> "testProperty \"name\""
            Tasty -> "testProperty \"name\""
          lambda = if null prettyArgs then "" else '\\' : unwords prettyArgs ++ " -> "
          prefix = maybe "" (++ " ==> ") prettyPred
      in how ++ " $ " ++ lambda ++ prefix ++ prettyLSig ++ " (\\h0 -> " ++ prettyLExpr ++ ") " ++ prettyOp ++ " " ++ prettyRSig ++ " (\\h0 -> " ++ prettyRExpr ++ ")"
    Nothing ->
      let off = replicate (maxlen prettyPred - length prettyLExpr) ' '
          prefix = maybe "" (++ "  ==>  ") prettyPred
      in prefix ++ off ++ prettyLExpr ++ "  " ++ prettyOp ++ "  " ++ prettyRExpr

  maxlen p0 = maximum (map (\PPRProp{..} -> if prettyPred == p0 then length prettyLExpr else 0) obss)

  nf = T.getVariableBaseName (pprTypeInfos opts)

  pp :: Typeable s => E.Expr s h -> String
  pp = E.pp nf (isJust $ pprDejaFu opts)
