{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
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
  -- * Miscellaneous
  , funTys
  , typeArity
  , innerTy
  ) where

import           Data.Function (on)
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
-- Typeable 'T.TypeRep'. This is safe if 'HasTypeRep' would assign
-- that 'T.TypeRep', and so is unsafe if the monad or state cases
-- apply.
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
-- Miscellaneous

-- | The types of a function's argument and result. Returns @Nothing@
-- if applied to any type other than a function type.
funTys :: TypeRep -> Maybe (TypeRep, TypeRep)
funTys ty = case splitTyConApp ty of
    (con, [argTy, resultTy]) | con == funTyCon -> Just (argTy, resultTy)
    _ -> Nothing

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

-- | The function arrow.
funTyCon :: TyCon
funTyCon = typeRepTyCon (typeRep (Proxy :: Proxy (() -> ())))
