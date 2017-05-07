{-# LANGUAGE LambdaCase #-}

-- |
-- Module      : Test.CoCo.Rename
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : LambdaCase
--
-- Functions for projecting expressions into a consistent namespace.
module Test.CoCo.Rename where

import           Data.Typeable  (TypeRep)

import           Test.CoCo.Expr (Expr, environment)

-- | The @These@ type is like 'Either', but also has the case for when
-- we have both values.
data These a b
  = This a
  | That b
  | These a b
  deriving (Eq, Show)

-- | A projection into a common namespace.  This only makes sense for
-- the original two expressions it was generated from.
type Projection = [(These String String, TypeRep)]

-- | Find all type-correct ways of associating environment variables.
projections :: Expr s1 h1 -> Expr s2 h2 -> [Projection]
projections e1 e2 = projectionsFromEnv (environment e1) (environment e2)

-- | Like 'projections' but takes the lists of environment variables
-- directly.
projectionsFromEnv :: [(String, TypeRep)] -> [(String, TypeRep)] -> [Projection]
projectionsFromEnv t1 [] = [[(This v, ty) | (v, ty) <- t1]]
projectionsFromEnv [] t2 = [[(That v, ty) | (v, ty) <- t2]]
projectionsFromEnv ((vL, tyL):t1) t2 =
   map ((This vL, tyL) :) (projectionsFromEnv t1 t2)
   ++ [(These vL vR, tyL) : proj
      | x@(vR, tyR) <- t2
      , tyL == tyR
      , proj <- projectionsFromEnv t1 (filter (/=x) t2)
      ]

-- | Given a projection into a common namespace, produce a consistent
-- variable renaming. Variables of the same type, after the first,
-- will have a number appended starting from 1.
renaming :: (TypeRep -> Char) -> Projection -> ([(String, String)], [(String, String)])
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
renamings :: (TypeRep -> Char) -> Expr s1 h1 -> Expr s2 h2 -> [([(String, String)], [(String, String)])]
renamings varf t1 t2 = map (renaming varf) (projections t1 t2)

-- | Check if one projection is more general than another (this is a
-- partial ordering).
--
-- A projection with more unique variables (@This@ and @That@ values)
-- is \"more general\" than one with more merged variables (@These@
-- values). For some intuition, consider an extreme case:
--
-- @
-- f a b == g c d
-- f a b == g a b
-- @
--
-- Clearly if the first property is true, then the second will as
-- well. The first is more general in that it imposes fewer
-- constraints on the values of the variables. The latter is more
-- specific as it imposes two constraints.
isMoreGeneralThan :: Projection -> Projection -> Bool
isMoreGeneralThan ((these1, ty1):as) ((these2, ty2):bs)
  | ty1 /= ty2       = False
  | these1 == these2 = isMoreGeneralThan as bs
  | otherwise        = case (these1, these2) of
      (This a, These x y) -> a == x && (That y, ty1) `elem` as && isMoreGeneralThan (filter (/=(That y, ty1)) as) bs
      (That b, These x y) -> b == y && (This x, ty1) `elem` as && isMoreGeneralThan (filter (/=(This x, ty1)) as) bs
      _ -> False
isMoreGeneralThan [] [] = True
isMoreGeneralThan _ _ = False
