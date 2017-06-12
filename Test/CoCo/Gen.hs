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

import           Control.Arrow      (second, (***))
import           Control.Monad      (filterM, guard)
import           Data.Function      (on)
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M
import           Data.List          (partition)
import           Data.Maybe         (fromMaybe, maybeToList)
import           Data.Proxy         (Proxy(..))
import           Data.Semigroup     ((<>))
import           Data.Set           (Set)
import qualified Data.Set           as S
import           Data.Typeable      (TypeRep, Typeable, splitTyConApp, typeRep)

import           Test.CoCo.Ann
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
data Generator s o x = Generator
  { tiers      :: IntMap (Set (Schema s, (Maybe (Ann s o x), Ann s o x)))
  , sofar      :: Int
  , pures      :: Set (Term s)
  , forbiddens :: Set (Term s)
  , tyinfos    :: [(TypeRep, TypeInfo)]
  }

-- | Create a new generator from a collection of basic expressions.
newGenerator :: (Typeable s, Ord o, Ord x)
  => [(TypeRep, TypeInfo)] -> [(Schema s, Ann s o x)] -> Generator s o x
newGenerator typeInfos baseTerms = Generator
  { tiers   = merge
    [ M.singleton
      (exprSize e)
      -- TODO: filter equivalent terms in this initial set?
      (S.singleton (e, (Nothing, a { theTerms = allTerms (getVariableBaseName typeInfos) e })))
    | (e,a) <- baseTerms ]
  , sofar   = 0
  , pures   = S.fromList $ concat
    [ allTerms (getVariableBaseName typeInfos) e | (e,_) <- baseTerms, isPure e ]
  , forbiddens = S.empty
  , tyinfos = typeInfos
  }

-- | Generate the next tier.
stepGenerator :: (Typeable s, Ord o, Ord x)
  => (Ann s o x -> Ann s o x -> Schema s -> Bool)
  -- ^ Annotation of first expr, annotation of second expr, combined expr.
  -> Generator s o x -> Generator s o x
stepGenerator check g = g { tiers = tiers', sofar = sofar', pures = pures', forbiddens = forbiddens' } where
  sofar' = sofar g + 1
  tiers' = merge
    [ tiers g
    , M.singleton sofar' funAps
    , M.singleton sofar' binds
    ]
  pures' =
    let new = filter isPure . map fst . S.toList $ M.findWithDefault S.empty sofar' tiers'
        getTerms = concatMap $ allTerms (getVariableBaseName (tyinfos g))
    in pures g `S.union` S.fromList (getTerms new)
  forbiddens' = forbiddens g `S.union` S.fromList newForbiddens

  -- produce new terms by function application.
  (newForbiddens, funAps) = mkTerms 0 $ \terms candidates ->
    [ (forbidden, (new, (Nothing, (snd fAnn <> snd eAnn) { theTerms = schemaTerms })))
      | (f, fAnn) <- terms
      , (e, eAnn) <- candidates
      , new <- maybeToList (f $$ e)
      , check (snd fAnn) (snd eAnn) new
      , let varf = getVariableBaseName (tyinfos g)
      , let newTerms = filter (not . hasForbiddenSubterm varf (S.toList $ forbiddens g)) (allTerms varf new)
      , let (forbidden, schemaTerms) =
              if isPure new
              -- new pure schemas cannot be equivalent to any existing ones
              then foldr (\p (fs, ts) ->
                            let (fs', ts') = partitionEquivalent (tyinfos g) p ts
                            in (fs++fs', ts')) ([], newTerms) . S.toList $ pures g
              else ([], newTerms)
    ]

  -- produce new terms by monad-binding variables.
  binds = snd . mkTerms 1 $ \terms candidates ->
    [ ([], (new, (Nothing, (snd bAnn <> snd eAnn) { theTerms = schemaTerms })))
      | (b, bAnn) <- terms
      -- don't allow a binder which is a hole
      , not (isHole b)
      , (e, eAnn) <- candidates
      , holeset <- powerset . map fst $ holes e
      , new <- maybeToList (bind holeset b e)
      , check (snd bAnn) (snd eAnn) new
      , let varf = getVariableBaseName (tyinfos g)
      , let schemaTerms = filter (not . hasForbiddenSubterm varf (S.toList $ forbiddens g)) (allTerms varf new)
    ]

  -- produce new terms
  mkTerms n f = M.foldMapWithKey go (tiers g) where
    go tier terms = (concat *** S.fromList) . unzip $
      let candidates = getTier (sofar g + 1 - tier - n) g
      in f (S.toList terms) (S.toList candidates)

  powerset = filterM (const [False,True])

-- | Get the terms of a given size.
getTier :: Int -> Generator s o x -> Set (Schema s, (Maybe (Ann s o x), Ann s o x))
getTier tier = M.findWithDefault S.empty tier . tiers

-- | Apply a function to every expression in a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
mapTier :: (Ord o, Ord x)
  => ((Schema s, (Maybe (Ann s o x), Ann s o x)) -> (Schema s, (Maybe (Ann s o x), Ann s o x)))
  -> Int -> Generator s o x -> Generator s o x
mapTier = adjustTier . S.map

-- | Filter expressions in a tier.
filterTier
  :: ((Schema s, (Maybe (Ann s o x), Ann s o x)) -> Bool)
  -> Int
  -> Generator s o x -> Generator s o x
filterTier = adjustTier . S.filter

-- | Apply a function to a tier.
--
-- It is IMPORTANT that this function does not make any expressions
-- larger or smaller! 'stepGenerator' assumes that every expression in
-- a tier is of the correct size, and it WILL NOT behave properly if
-- this invariant is broken!
adjustTier
  :: (Set (Schema s, (Maybe (Ann s o x), Ann s o x)) -> Set (Schema s, (Maybe (Ann s o x), Ann s o x)))
  -> Int
  -> Generator s o x -> Generator s o x
adjustTier f tier g = g { tiers = M.adjust f tier (tiers g) }

-- | Get the highest size generated so far.
maxTier :: Generator s o x -> Int
maxTier = sofar


-------------------------------------------------------------------------------
-- Utilities

-- | Merge a list of maps of lists.
merge :: Ord a => [IntMap (Set a)] -> IntMap (Set a)
merge = M.unionsWith S.union

-- | Check if a schema has a non-monadic and non-function result type.
isPure :: Typeable s => Schema s -> Bool
isPure e = not $ ety `ceq` cty || ety `ceq` fty where
  ceq = (==) `on` fst . splitTyConApp
  ety = exprTypeRep e
  cty = typeRep (Proxy :: Proxy (Concurrency ()))
  fty = typeRep (Proxy :: Proxy (() -> ()))

-- | Given a collection of forbidden subterms, check if the given term
-- contains one.
hasForbiddenSubterm :: Typeable s => (TypeRep -> Char) -> [Term s] -> Term s -> Bool
hasForbiddenSubterm varf fs0 t0 = or [match t f | t <- subterms t0, f <- fs0] where
  match t1 t2 =
    exprSize    t1 == exprSize    t2 &&
    exprTypeRep t1 == exprTypeRep t2 &&
    any (\(r1,r2) -> rename r1 t1 == rename r2 t2) (renamings varf t1 t2)

-- | Given one pure term and a collection of other pure terms return
-- the equivalent terms (in the left) and the inequivalent ones (in
-- the right).
partitionEquivalent :: Typeable s => [(TypeRep, TypeInfo)] -> Term s ->  [Term s] -> ([Term s], [Term s])
partitionEquivalent typeInfos t0 ts = fromMaybe ([], ts) $ do
    guard $ all ((exprTypeRep t0 ==) . exprTypeRep) ts
    tyinfo <- lookup (exprTypeRep t0) typeInfos
    pure $ partition (checkEquiv tyinfo t0) ts
  where
    varf = getVariableBaseName typeInfos

    checkEquiv tyinfo t1 t2 = go (renamings varf t1 t2) where
      go (r:rs) =
        let t1' = rename (fst r) t1
            t2' = rename (snd r) t2
            equiv = and [ dynEq tyinfo d1 d2
                        | as <- assign typeInfos $ environment t1' ++ environment t2'
                        , d1 <- maybeToList (evaluateDynPure t1' as)
                        , d2 <- maybeToList (evaluateDynPure t2' as)
                        ]
        in equiv || go rs
      go [] = False

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
