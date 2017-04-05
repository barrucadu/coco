{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : Test.Spec.Rename
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : LambdaCase
--
-- Functions for projecting expressions into a consistent namespace.
module Test.Spec.Rename where

import Control.Arrow (second)
import Data.Typeable (TypeRep)

import Test.Spec.Expr (Expr, environment)
import Test.Spec.Type (rawTypeRep)

-- | The @These@ type is like 'Either', but also has the case for when
-- we have both values.
data These a b
  = This a
  | That b
  | These a b
  deriving Show

-- | Find all type-correct ways of associating environment variables.
projections :: Expr s1 m1 h1 -> Expr s2 m2 h2 -> [[(These String String, TypeRep)]]
projections e1 e2 = go (env e1) (env e2) where
  go t1 [] = [[(This v, ty) | (v, ty) <- t1]]
  go [] t2 = [[(That v, ty) | (v, ty) <- t2]]
  go ((vL, tyL):t1) t2 =
   map ((This vL, tyL) :) (go t1 t2) ++
   concat [map ((These vL vR, tyL) :) (go t1 (filter (/=x) t2)) | x@(vR, tyR) <- t2, tyL == tyR]

  env = map (second rawTypeRep) . environment

-- | Given a projection into a common namespace, produce a consistent
-- variable renaming. Variables of the same type, after the first,
-- will have a number appended starting from 1.
renaming :: (TypeRep -> Char) -> [(These String String, TypeRep)] -> ([(String, String)], [(String, String)])
renaming varf = go [] ([], []) where
  go e x ((these, ty):rest) =
    let name = varf ty
    in rename e x name (maybe 0 (+1) $ lookup name e) these rest
  go _ x [] = x

  rename e ~(l, r) name n = let name' = if n == (0::Int) then [name] else name : show n in \case
    This  vL    -> go ((name, n):e) ((vL, name'):l,             r)
    That     vR -> go ((name, n):e) (l,             (vR, name'):r)
    These vL vR -> go ((name, n):e) ((vL, name'):l, (vR, name'):r)

-- | Find all consistent renamings of a pair of expressions.
renamings :: (TypeRep -> Char) -> Expr s1 m1 h1 -> Expr s2 m2 h2 -> [([(String, String)], [(String, String)])]
renamings varf t1 t2 = map (renaming varf) (projections t1 t2)
