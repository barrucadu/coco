{-# LANGUAGE StrictData #-}

-- |
-- Module      : Test.CoCo.Gen
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : StrictData
--
-- Generating well-typed dynamic expressions from smaller components.
module Test.CoCo.Gen where

import           Control.Arrow      (second)
import           Control.Monad      (filterM, guard)
import           Data.Function      (on)
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M
import           Data.Maybe         (fromMaybe, maybeToList)
import           Data.Proxy         (Proxy(..))
import           Data.Semigroup     (Semigroup, (<>))
import           Data.Set           (Set)
import qualified Data.Set           as S
import           Data.Typeable      (TypeRep, Typeable, splitTyConApp, typeRep)

import           Test.CoCo.Eval     (numVariants)
import           Test.CoCo.Expr
import           Test.CoCo.Monad    (Concurrency)
import           Test.CoCo.Rename   (renamings)
import           Test.CoCo.Type     (Dynamic)
import           Test.CoCo.TypeInfo (TypeInfo(..), getTypeValues,
                                     getVariableBaseName)
import           Test.CoCo.Util     (ordNubOn)


-------------------------------------------------------------------------------
-- Controlled generation

-- | A generator of expressions.
data Generator s ann = Generator
  { tiers   :: IntMap (Set (Schema s, ann))
  , sofar   :: Int
  , pures   :: Set (Schema s)
  , tyinfos :: [(TypeRep, TypeInfo)]
  }

-- | Create a new generator from a collection of basic expressions.
newGenerator :: (Monoid ann, Ord ann, Typeable s) => [(TypeRep, TypeInfo)] -> [Schema s] -> Generator s ann
newGenerator typeInfos = newGenerator' typeInfos . map (\e -> (e, mempty))

-- | Like 'newGenerator', but use an explicit default value.
newGenerator' :: (Ord ann, Typeable s) => [(TypeRep, TypeInfo)] -> [(Schema s, ann)] -> Generator s ann
newGenerator' typeInfos baseTerms = Generator
  { tiers   = merge [M.singleton (exprSize e) (S.singleton s) | s@(e,_) <- baseTerms]
  , sofar   = 0
  , pures   = S.fromList [e | (e,_) <- baseTerms, isPure e]
  , tyinfos = typeInfos
  }

-- | Generate the next tier.
stepGenerator :: (Semigroup ann, Ord ann, Typeable s)
  => (ann -> ann -> Schema s -> Bool)
  -- ^ Annotation of first expr, annotation of second expr, combined expr.
  -> Generator s ann -> Generator s ann
stepGenerator check g = g { tiers = tiers', sofar = sofar', pures = pures' } where
  sofar' = sofar g + 1
  tiers' = merge
    [ tiers g
    , M.singleton sofar' funAps
    , M.singleton sofar' binds
    ]
  pures' =
    let new = (map fst . S.toList) (M.findWithDefault S.empty sofar' tiers')
    in pures g `S.union` S.fromList (filter isPure new)

  -- produce new terms by function application.
  funAps = mkTerms 0 $ \terms candidates ->
    [ (new, fAnn <> eAnn)
      | (f, fAnn) <- terms
      , (e, eAnn) <- candidates
      , new <- maybeToList (f $$ e)
      , check fAnn eAnn new
      , if isPure new
        -- new pure schemas cannot be equivalent to any existing ones
        then all (not . equivalent (tyinfos g) new) (pures g)
        else True
    ]

  -- produce new terms by monad-binding variables.
  binds = mkTerms 1 $ \terms candidates ->
    [ (new, bAnn <> eAnn)
      | (b, bAnn) <- terms
      -- don't allow a binder which is a hole
      , not (isHole b)
      , (e, eAnn) <- candidates
      , holeset <- powerset . map fst $ holes e
      , new <- maybeToList (bind holeset b e)
      , check bAnn eAnn new
    ]

  -- produce new terms
  mkTerms n f = M.foldMapWithKey go (tiers g) where
    go tier terms = S.fromList $
      let candidates = getTier (sofar g + 1 - tier - n) g
      in f (S.toList terms) (S.toList candidates)

  powerset = filterM (const [False,True])

-- | Get the terms of a given size.
getTier :: Int -> Generator s ann -> Set (Schema s, ann)
getTier tier = M.findWithDefault S.empty tier . tiers

-- | Apply a function to every expression in a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
mapTier :: Ord ann => ((Schema s, ann) -> (Schema s, ann)) -> Int -> Generator s ann -> Generator s ann
mapTier = adjustTier . S.map

-- | Filter expressions in a tier.
filterTier :: ((Schema s, ann) -> Bool) -> Int -> Generator s ann -> Generator s ann
filterTier = adjustTier . S.filter

-- | Apply a function to a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
adjustTier :: (Set (Schema s, ann) -> Set (Schema s, ann)) -> Int -> Generator s ann -> Generator s ann
adjustTier f tier g = g { tiers = M.adjust f tier (tiers g) }

-- | Get the highest size generated so far.
maxTier :: Generator s ann -> Int
maxTier = sofar


-------------------------------------------------------------------------------
-- Utilities

-- | Merge a list of maps of lists.
merge :: Ord a => [IntMap (Set a)] -> IntMap (Set a)
merge = M.unionsWith S.union

-- | Check if a schema is pure (has a non-monadic result type).
isPure :: Typeable s => Schema s -> Bool
isPure e = not $ exprTypeRep e `ceq` typeRep (Proxy :: Proxy (Concurrency ())) where
  ceq = (==) `on` fst . splitTyConApp

-- | Check if two pure schemas are equivalent.
equivalent :: Typeable s => [(TypeRep, TypeInfo)] -> Schema s -> Schema s -> Bool
equivalent typeInfos e1 e2 = fromMaybe False $ do
  let varf = getVariableBaseName typeInfos
  let t1s = allTerms varf e1
  let t2s = allTerms varf e2
  guard (exprTypeRep e2 == exprTypeRep e2)
  tyinfo <- lookup (exprTypeRep e1) typeInfos
  pure (and [ dynEq tyinfo d1 d2
            | t1 <- t1s
            , t2 <- t2s
            , r  <- renamings varf t1 t2
            , let t1' = rename (fst r) t1
            , let t2' = rename (snd r) t2
            , as  <- assign typeInfos $ environment t1' ++ environment t2'
            , d1  <- maybeToList (evaluateDynPure t1' as)
            , d2  <- maybeToList (evaluateDynPure t2' as)
            ])

-- | Produce a list of assignments to free variables in an
-- environment.
--
-- 'numVariants' values will be taken of each and zipped together
-- (producing @numVariants^(length env)@ assignments).
assign
  :: [(TypeRep, TypeInfo)]
  -- ^ Information about types.  There MUST be an entry for every hole
  -- type!
  -> [(String, TypeRep)]
  -- ^ The free variables.
  -> [[(String, Dynamic)]]
assign typeInfos = go . ordNubOn fst . map (second enumerateValues) where
  go :: [(String, [Dynamic])] -> [[(String, Dynamic)]]
  go ((var, dyns):free) =
    [ (var, dyn) : as
    | dyn <- take numVariants dyns
    , as  <- go free
    ]
  go [] = [[]]

  enumerateValues = getTypeValues typeInfos
