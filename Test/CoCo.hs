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
  , E.hole
  , E.stateVar
    -- * Types
  , T.TypeInfo(..)
  , T.defaultTypeInfos
  , T.makeTypeInfo
  , T.toDyn
    -- * Miscellaneous
  , (|||)
  , prettyPrint
  ) where

import           Control.Monad            (void)
import           Control.Monad.Conc.Class (readMVar, spawn)
import           Data.List                (sortOn)
import           Data.Typeable            (TypeRep)

import qualified Test.CoCo.Discover       as D
import qualified Test.CoCo.Expr           as E
import qualified Test.CoCo.Logic          as L
import qualified Test.CoCo.Monad          as M
import qualified Test.CoCo.Sig            as S
import qualified Test.CoCo.Type           as T
import qualified Test.CoCo.TypeInfo       as T

-- | Concurrent composition. Waits for both component computations to
-- finish.
(|||) :: M.Concurrency a -> M.Concurrency b -> M.Concurrency ()
a ||| b = do
  j <- spawn a
  void b
  void (readMVar j)

-- | Pretty-print a list of observations.
prettyPrint :: [(TypeRep, T.TypeInfo)] -> [L.Observation] -> IO ()
prettyPrint typeInfos obss0 = mapM_ (putStrLn . pad) (sortOn cmp obss) where
  obss = map go obss0 where
    go (L.Equiv   e1 e2) = (Nothing, E.pp nf e1, "===", E.pp nf e2)
    go (L.Refines e1 e2) = (Nothing, E.pp nf e1, "=[=", E.pp nf e2)
    go (L.Implied p obs) = let (Nothing, e1, t, e2) = go obs in (Just p, e1, t, e2)

  cmp (p, e1, _, e2) = (maybe 0 length p, p, length e1, e1, length e2, e2)

  pad (p, e1, t, e2) =
    let off = replicate (maxlen p - length e1) ' '
        prefix = maybe "" (++ "  ==>  ") p
    in prefix ++ off ++ e1 ++ "  " ++ t ++ "  " ++ e2

  maxlen p0 = maximum (map (\(p, e1, _, _) -> if p == p0 then length e1 else 0) obss)

  nf = T.getVariableBaseName typeInfos
