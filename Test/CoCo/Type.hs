{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Test.CoCo.Type
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs, KindSignatures, ScopedTypeVariables
--
-- A reimplementation of Data.Dynamic, but twisted to my own malign
-- purposes. This is basically all necessary because the constructor
-- for
-- @<http://hackage.haskell.org/package/base/docs/Data-Dynamic.html#t:Dynamic
-- Data.Dynamic.Dynamic>@ isn't exposed. On the other hand, if it was
-- exposed it would be trivial to violate its invariant and write
-- unsafeCoerce, swings and roundabouts...
--
-- This is not good code. Do not come here to learn, unless you need
-- to solve the same problem. Here be dragons.
module Test.CoCo.Type
  ( -- * Dynamic
    Dynamic
  , toDyn
  , fromDyn
  , anyFromDyn
  , dynTypeRep
  , dynApp
  -- ** Type-safe coercions
  , unwrapFunctorDyn
  -- ** Unsafe operations
  , unsafeToDyn
  , unsafeWrapFunctorDyn
  -- * Types
  , funTys
  , funArgTys
  , typeArity
  , innerTy
  -- ** Polymorphism
  -- *** Type variables
  , TyVar(..)
  , A
  , B
  , C
  , D
  , isTyVar
  -- *** Unification
  , unify
  , unify'
  , unifyAccum
  , polyFunResultTy
  -- *** Environments
  , TypeEnv
  , assignTys
  , assignDynTys
  ) where

import           Data.Function (on)
import           Data.List     (nub)
import           Data.Maybe    (fromMaybe, isJust)
import           Data.Proxy    (Proxy(..))
import           Data.Typeable
import           GHC.Base      (Any)
import           Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- Dynamic

-- | A dynamically-typed value, with state type @s@ and monad type
-- @m@.
data Dynamic where
  Dynamic :: TypeRep -> Any -> Dynamic

instance Show Dynamic where
  show d = "Dynamic <" ++ show (dynTypeRep d) ++ ">"

-- | This only compares types.
instance Eq Dynamic where
  (==) = (==) `on` dynTypeRep

-- | This only compares types.
instance Ord Dynamic where
  compare = compare `on` dynTypeRep

-- | Convert a static value into a dynamic one.
toDyn :: Typeable a => a -> Dynamic
toDyn a = Dynamic (typeOf a) (unsafeCoerce a)

-- | Try to convert a dynamic value back into a static one.
fromDyn :: Typeable a => Dynamic -> Maybe a
fromDyn (Dynamic ty x) = case unsafeCoerce x of
  r | typeOf r == ty -> Just r
    | otherwise -> Nothing

-- | Throw away type information and get the 'Any' from a 'Dynamic'.
anyFromDyn :: Dynamic -> Any
anyFromDyn (Dynamic _ x) = x

-- | Get the type of a dynamic value.
dynTypeRep :: Dynamic -> TypeRep
dynTypeRep (Dynamic ty _) = ty

-- | Apply a dynamic function to a dynamic value, if the types match.
dynApp :: Dynamic -> Dynamic -> Maybe Dynamic
dynApp (Dynamic t1 f) (Dynamic t2 x) = case t1 `funResultTy` t2 of
  Just t3 -> Just (Dynamic t3 ((unsafeCoerce f) x))
  Nothing -> Nothing


-------------------------------------------------------------------------------
-- Type-safe coercions

-- | \"Extract\" a functor from a dynamic value
unwrapFunctorDyn :: forall f. (Functor f, Typeable f) => Dynamic -> Maybe (f Dynamic)
unwrapFunctorDyn (Dynamic ty a) = case innerTy (Proxy :: Proxy f) ty of
  Just ty' -> Just $ Dynamic ty' <$> unsafeCoerce a
  Nothing  -> Nothing


-------------------------------------------------------------------------------
-- Unsafe operations

-- | Convert a static value into a dynamic one, using a regular normal
-- Typeable 'TypeRep'. This is safe if 'HasTypeRep' would assign that
-- 'TypeRep', and so is unsafe if the monad or state cases apply.
unsafeToDyn :: TypeRep -> a -> Dynamic
unsafeToDyn ty = Dynamic ty . unsafeCoerce

-- | \"Push\" a functor inside a dynamic value, given the type of the
-- resultant value.
--
-- This is unsafe because if the type is incorrect and the value is
-- later used as that type, good luck.
unsafeWrapFunctorDyn :: Functor f => TypeRep -> f Dynamic -> Dynamic
unsafeWrapFunctorDyn ty fdyn = Dynamic ty (unsafeCoerce $ fmap anyFromDyn fdyn)


-------------------------------------------------------------------------------
-- Types

-- | A polymorphic type variable.  The parameter uniquely identifies
-- this variable within a type.
data TyVar t = TyVar
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | A polymorphic type variable.
type A = TyVar 0

-- | A polymorphic type variable.
type B = TyVar 1

-- | A polymorphic type variable.
type C = TyVar 2

-- | A polymorphic type variable.
type D = TyVar 3

-- | Check if a type is a variable.
isTyVar :: TypeRep -> Bool
isTyVar = ((==) `on` (fst . splitTyConApp)) (typeRep (Proxy :: Proxy A))

-- | An environment of type bindings.
type TypeEnv = [(TypeRep, TypeRep)]

-- | Attempt to unify two types.
unify :: TypeRep -> TypeRep -> Maybe TypeEnv
unify = unify' True

-- | Attempt to unify two types.
unify'
  :: Bool
  -- ^ Whether to allow either type to be a naked type variable at
  -- this level (always true in lower levels).
  -> TypeRep -> TypeRep -> Maybe TypeEnv
unify' b tyA tyB
    -- check equality
    | tyA == tyB = Just []
    -- check if one is a naked type variable
    | isTyVar tyA = if not b || occurs tyA tyB then Nothing else Just [(tyA, tyB)]
    | isTyVar tyB = if not b || occurs tyB tyA then Nothing else Just [(tyB, tyA)]
    -- deconstruct each and attempt to unify subcomponents
    | otherwise =
      let (conA, argsA) = splitTyConApp tyA
          (conB, argsB) = splitTyConApp tyB
      in if conA == conB && length argsA == length argsB
         then unifyAccum True id argsA argsB
         else Nothing
  where
    -- check if a type occurs in another
    occurs needle haystack = needle == haystack || any (occurs needle) (snd (splitTyConApp haystack))

-- | An accumulating unify: attempts to unify two lists of types
-- pairwise and checks that the resulting assignments do not conflict
-- with the current type environment.
unifyAccum :: Bool -> (Maybe TypeEnv -> Maybe TypeEnv) -> [TypeRep] -> [TypeRep] -> Maybe TypeEnv
unifyAccum b f as bs = foldr go (Just []) (zip as bs) where
  go (tyA, tyB) (Just env) =
    unifyTypeEnvs b env =<< f (unify' b tyA tyB)
  go _ Nothing = Nothing

-- | Unify two type environments, if possible.
unifyTypeEnvs :: Bool -> TypeEnv -> TypeEnv -> Maybe TypeEnv
unifyTypeEnvs b env1 env2 = foldr go (Just []) (nub $ map fst env1 ++ map fst env2) where
  go tyvar acc@(Just env) = case (lookup tyvar env, lookup tyvar env1, lookup tyvar env2) of
    (_, Just ty1, Just ty2) -> unifyTypeEnvs b env . ((tyvar, ty1):) =<< unify' b ty1 ty2
    (x, Just ty1, _)
      | isJust x  -> unifyTypeEnvs b env [(tyvar, ty1)]
      | otherwise -> Just ((tyvar, ty1):env)
    (x, _, Just ty2)
      | isJust x  -> unifyTypeEnvs b env [(tyvar, ty2)]
      | otherwise -> Just ((tyvar, ty2):env)
    _ -> acc
  go _ Nothing = Nothing

-- | Applies a type to a given function type, if the types match. This
-- performs unification if the @A@, @B@, @C@, or @D@ types are
-- involved.
polyFunResultTy :: TypeRep -> TypeRep -> Maybe (TypeEnv, TypeRep)
polyFunResultTy fty aty = do
  (argTy, resultTy) <- funTys fty
  assignments       <- unify aty argTy
  pure (assignments, assignTys assignments resultTy)

-- | Assign type variables in a type
assignTys :: TypeEnv -> TypeRep -> TypeRep
assignTys assignments ty
  | isTyVar ty = fromMaybe ty (lookup ty assignments)
  | otherwise = let (con, args) = splitTyConApp ty in mkTyConApp con (map (assignTys assignments) args)

-- | Assign type variables in a dynamic value
assignDynTys :: TypeEnv -> Dynamic -> Dynamic
assignDynTys assignments (Dynamic ty x) = Dynamic (assignTys assignments ty) x

-- | The arity of a type. Non-function types have an arity of 0.
typeArity :: TypeRep -> Int
typeArity ty = case splitTyConApp ty of
  (con, [_, resultType]) | con == funTyCon -> 1 + typeArity resultType
  _ -> 0

-- | Extract the type inside a constructor.
innerTy :: forall proxy f. Typeable f => proxy (f :: * -> *) -> TypeRep -> Maybe TypeRep
innerTy p ty = case splitTyConApp ty of
    (tyCon, tyArgs)
      | tyCon == ftyCon && not (null tyArgs) && init tyArgs == ftyArgs
        -> Just (last tyArgs)
    _ -> Nothing
  where
    (ftyCon, ftyArgs) = splitTyConApp (typeRep p)

-- | The types of a function's argument and result. Returns @Nothing@
-- if applied to any type other than a function type.
funTys :: TypeRep -> Maybe (TypeRep, TypeRep)
funTys ty = case splitTyConApp ty of
  (con, [argTy, resultTy]) | con == funTyCon -> Just (argTy, resultTy)
  _ -> Nothing

-- | Like 'funTys', but returns the list of all arguments and the
-- final result.
funArgTys :: TypeRep -> Maybe ([TypeRep], TypeRep)
funArgTys ty = case funTys ty of
    Just (argTy, resultTy) -> Just (go [argTy] resultTy)
    Nothing -> Nothing
  where
    go argTys resultTy = case funTys resultTy of
      Just (argTy, resultTy') -> go (argTy:argTys) resultTy'
      Nothing -> (reverse argTys, resultTy)

-- | The function arrow.
funTyCon :: TyCon
funTyCon = typeRepTyCon (typeRep (Proxy :: Proxy (() -> ())))
