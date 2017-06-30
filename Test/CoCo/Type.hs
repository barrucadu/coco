{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}

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
  , dynType
  , dynApp
  -- ** Type-safe coercions
  , unwrapFunctorDyn
  -- ** Unsafe operations
  , unsafeToDyn
  , unsafeWrapFunctorDyn
  , unsafeSetType
  -- * Types
  , Type
  , toType
  , typeRep
  , typeOf
  , tyCon
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
  -- *** Unification
  , unifies
  , UnifyM
  , runUnify
  , polyApplyFunTy
  , polyApplyFunTy'
  , U.applyBindings
  , dynApplyBindings
  ) where

import qualified Control.Monad.Except       as E
import           Control.Monad.Trans.Class  (lift)
import qualified Control.Unification        as U
import qualified Control.Unification.IntVar as U
import qualified Control.Unification.Types  as U
import           Data.Char                  (ord)
import           Data.Function              (on)
import qualified Data.Functor.Identity      as I
import           Data.List                  (foldl')
import           Data.Maybe                 (isJust)
import           Data.Proxy                 (Proxy(..))
import qualified Data.Typeable              as T
import           GHC.Base                   (Any)
import           Unsafe.Coerce              (unsafeCoerce)

-------------------------------------------------------------------------------
-- Dynamic

-- | A dynamically-typed value, with state type @s@ and monad type
-- @m@.
data Dynamic where
  Dynamic :: Type -> Any -> Dynamic

instance Show Dynamic where
  show d = "Dynamic <" ++ show (dynType d) ++ ">"

-- | This only compares types.
instance Eq Dynamic where
  (==) = (==) `on` dynType

-- | This only compares types.
instance Ord Dynamic where
  compare = compare `on` dynType

-- | Convert a static value into a dynamic one.
toDyn :: T.Typeable a => a -> Dynamic
toDyn a = Dynamic (typeOf a) (unsafeCoerce a)

-- | Try to convert a dynamic value back into a static one.
fromDyn :: T.Typeable a => Dynamic -> Maybe a
fromDyn (Dynamic ty x) = case unsafeCoerce x of
  r | typeOf r `unifies` ty -> Just r
    | otherwise -> Nothing

-- | Throw away type information and get the 'Any' from a 'Dynamic'.
anyFromDyn :: Dynamic -> Any
anyFromDyn (Dynamic _ x) = x

-- | Get the type of a dynamic value.
dynType :: Dynamic -> Type
dynType (Dynamic ty _) = ty

-- | Apply a dynamic function to a dynamic value, if the types match.
dynApp :: Dynamic -> Dynamic -> Maybe Dynamic
dynApp (Dynamic t1 f) (Dynamic t2 x) = case t1 `polyApplyFunTy` t2 of
  Just (_, t3) -> Just (Dynamic t3 ((unsafeCoerce f) x))
  Nothing -> Nothing


-------------------------------------------------------------------------------
-- Type-safe coercions

-- | \"Extract\" a functor from a dynamic value
unwrapFunctorDyn :: forall f. (Functor f, T.Typeable f) => Dynamic -> Maybe (f Dynamic)
unwrapFunctorDyn (Dynamic ty a) = case innerTy (Proxy :: Proxy f) ty of
  Just ty' -> Just $ Dynamic ty' <$> unsafeCoerce a
  Nothing  -> Nothing


-------------------------------------------------------------------------------
-- Unsafe operations

-- | Convert a static value into a dynamic one, using a regular normal
-- Typeable 'TypeRep'. This is safe if 'Typeable' would assign that
-- 'Type', and so is unsafe if the monad or state cases apply.
unsafeToDyn :: Type -> a -> Dynamic
unsafeToDyn ty = Dynamic ty . unsafeCoerce

-- | \"Push\" a functor inside a dynamic value, given the type of the
-- resultant value.
--
-- This is unsafe because if the type is incorrect and the value is
-- later used as that type, good luck.
unsafeWrapFunctorDyn :: Functor f => Type -> f Dynamic -> Dynamic
unsafeWrapFunctorDyn ty fdyn =
  Dynamic ty (unsafeCoerce $ fmap anyFromDyn fdyn)

-- | Change the type of a dynamic value to an arbitrary value.
unsafeSetType :: Type -> Dynamic -> Dynamic
unsafeSetType ty (Dynamic _ v) = Dynamic ty v


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

-- | A representation of Haskell types.
data TypeF ty = TypeF T.TyCon [ty]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance U.Unifiable TypeF where
  zipMatch (TypeF con1 args1) (TypeF con2 args2)
    | con1 /= con2  = Nothing
    | length args1 /= length args2 = Nothing
    | otherwise = Just (TypeF con1 $ zipWith (curry Right) args1 args2)

-- | Types with type variables.
type Type = U.UTerm TypeF U.IntVar

instance Eq Type where
  (U.UTerm (TypeF con1 args1)) == (U.UTerm (TypeF con2 args2)) =
    con1 == con2 && length args1 == length args2 && and (zipWith (==) args1 args2)
  (U.UVar v1) == (U.UVar v2) = v1 == v2
  _ == _ = False

instance Ord Type where
  compare (U.UTerm _) (U.UVar _)  = GT
  compare (U.UVar _)  (U.UTerm _) = LT
  compare (U.UTerm (TypeF con1 args1)) (U.UTerm (TypeF con2 args2)) = mconcat $
    con1 `compare` con2 : length args1 `compare` length args2 : zipWith compare args1 args2
  compare (U.UVar (U.IntVar v1)) (U.UVar (U.IntVar v2)) = v1 `compare` v2

-- | Convert a 'TypeRep' into a 'Type'.
toType :: T.TypeRep -> Type
toType ty =
  let (con, args) = T.splitTyConApp ty
      (vcon, _)   = T.splitTyConApp (T.typeRep (Proxy :: Proxy A))
  in if con == vcon
     then U.UVar (U.IntVar (foldl' (\n c -> ord c + n * 10) 0 (show args)))
     else U.UTerm (TypeF con (map toType args))

-- | Get the 'Type' of a proxy.
typeRep :: T.Typeable a => proxy a -> Type
typeRep = toType . T.typeRep

-- | Get the 'Type' of a value.
typeOf :: T.Typeable a => a -> Type
typeOf = toType . T.typeOf

-- | Get the 'T.TyCon' of a type.
tyCon :: Type -> Maybe T.TyCon
tyCon (U.UTerm (TypeF con _)) = Just con
tyCon _ = Nothing

type UnifyM = E.ExceptT (U.UFailure TypeF U.IntVar) (U.IntBindingT TypeF I.Identity)

-- | Run a unification computation.
runUnify :: UnifyM a -> Maybe a
runUnify =
  either (const Nothing) Just . I.runIdentity . U.evalIntBindingT . E.runExceptT

-- | Check if two types unify.
unifies :: Type -> Type -> Bool
unifies ty1 ty2 = isJust . runUnify $ do
  -- freshen type variables if there's any overlap
  vs1 <- lift (U.getFreeVars ty1)
  vs2 <- lift (U.getFreeVars ty2)
  (ty1', ty2') <-
    let f = if any (`elem` vs2) vs1 then U.freshen else pure
    in (,) <$> f ty1 <*> f ty2
  U.unify ty1' ty2'

-- | Applies a type to a given function type, if the types match. This
-- performs unification. The argument and result types are the two
-- return values.
polyApplyFunTy :: Type -> Type -> Maybe (Type, Type)
polyApplyFunTy fty xty = runUnify =<< polyApplyFunTy' fty xty

-- | Like 'polyApplyFunTy' but keeps the result in 'UnifyM'.
polyApplyFunTy' :: Type -> Type -> Maybe (UnifyM (Type, Type))
polyApplyFunTy' fty xty = case funTys fty of
  Just (argTy, resTy) -> Just $ do
      -- freshen type variables if there's any overlap
      fvs <- lift (U.getFreeVarsAll [argTy, resTy])
      xvs <- lift (U.getFreeVars xty)
      ([argTy', resTy'], [xty']) <-
        let f = if any (`elem` fvs) xvs then U.freshenAll else pure
        in (,) <$> f [argTy, resTy] <*> f [xty]
      -- perform unification and apply bindings in result
      uArgTy <- U.unify argTy' xty'
      uResTy <- U.applyBindings resTy'
      pure (uArgTy, uResTy)
  _ -> Nothing

-- | Apply the current type environment bindings to a 'Dynamic' value.
dynApplyBindings :: Dynamic -> UnifyM Dynamic
dynApplyBindings (Dynamic ty v) =
  Dynamic <$> U.applyBindings ty <*> pure v

-- | The arity of a type. Non-function types have an arity of 0.
typeArity :: Type -> Int
typeArity ty = case ty of
  U.UTerm (TypeF con [_, resTy]) | con == funTyCon -> 1 + typeArity resTy
  _ -> 0

-- | Extract the type inside a constructor.
innerTy :: forall proxy f. T.Typeable f => proxy (f :: * -> *) -> Type -> Maybe Type
innerTy p ty = case ty of
    U.UTerm (TypeF con args)
      | con == ftyCon && not (null args) && and (zipWith unifies (init args) (map toType ftyArgs))
        -> Just (last args)
    _ -> Nothing
  where
    (ftyCon, ftyArgs) = T.splitTyConApp (T.typeRep p)

-- | The types of a function's argument and result. Returns @Nothing@
-- if applied to any type other than a function type.
funTys :: Type -> Maybe (Type, Type)
funTys ty = case ty of
  U.UTerm (TypeF con [argTy, resTy])
    | con == funTyCon -> Just (argTy, resTy)
  _ -> Nothing

-- | Like 'funTys', but returns the list of all arguments and the
-- final result.
funArgTys :: Type -> Maybe ([Type], Type)
funArgTys ty = case funTys ty of
    Just (argTy, resTy) -> Just (go [argTy] resTy)
    Nothing -> Nothing
  where
    go argTys resTy = case funTys resTy of
      Just (argTy, resTy') -> go (argTy:argTys) resTy'
      Nothing -> (reverse argTys, resTy)

-- | The function arrow.
funTyCon :: T.TyCon
funTyCon = T.typeRepTyCon (T.typeRep (Proxy :: Proxy (() -> ())))
