{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : Test.Spec.Type
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : AllowAmbiguousTypes, FlexibleInstances, GADTs, KindSignatures, MagicHash, MultiParamTypeClasses, ScopedTypeVariables, TypeApplications, TypeOperators
--
-- A reimplementation of Data.Typeable and Data.Dynamic, but twisted
-- to my own malign purposes. This is basically all necessary because
-- the constructor for
-- @<http://hackage.haskell.org/package/base/docs/Data-Dynamic.html#t:Dynamic Data.Dynamic.Dynamic>@
-- isn't exposed. On the other hand, if it was exposed it would be
-- trivial to violate its invariant and write unsafeCoerce, swings and
-- roundabouts...
module Test.Spec.Type
  ( -- * Dynamic
    Dynamic
  , toDyn
  , fromDyn
  , dynTypeRep
  , dynApp

  -- * Typeable
  , HasTypeRep
  , TypeRep
  , (:~:)(..)
  , rawTypeRep
  , typeRep
  , typeOf
  , cast
  , eqT
  , gcast
  , funResultTy
  , typeArity
  , stateTypeRep
  ) where

import Data.Proxy (Proxy(..))
import Data.Typeable ((:~:)(..))
import qualified Data.Typeable as T
import GHC.Base (Any)
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- Dynamic

-- | A dynamically-typed value, with state type @s@ and monad type
-- @m@.
data Dynamic (s :: *) (m :: * -> *) where
  Dynamic :: Any -> TypeRep s m -> Dynamic s m

instance Show (Dynamic s m) where
  show d = "Dynamic <" ++ show (dynTypeRep d) ++ ">"

-- | Convert a static value into a dynamic one.
toDyn :: HasTypeRep s m a => a -> Dynamic s m
toDyn a = Dynamic (unsafeCoerce a) (typeOf a)

-- | Try to convert a dynamic value back into a static one.
fromDyn :: forall s m a. HasTypeRep s m a => Dynamic s m -> Maybe a
fromDyn (Dynamic x ty) = case unsafeCoerce x of
  r | typeOf r == ty -> Just r
    | otherwise -> Nothing

-- | Get the type of a dynamic value.
dynTypeRep :: Dynamic s m -> TypeRep s m
dynTypeRep (Dynamic _ ty) = ty

-- | Apply a dynamic function to a dynamic value, if the types match.
dynApp :: Dynamic s m -> Dynamic s m -> Maybe (Dynamic s m)
dynApp (Dynamic f t1) (Dynamic x t2) = case t1 `funResultTy` t2 of
  Just t3 -> Just (Dynamic ((unsafeCoerce f) x) t3)
  Nothing -> Nothing

-------------------------------------------------------------------------------
-- Typeable

-- | Typeable, but which can represent a non-Typeable state and monad
-- type.
class HasTypeRep (s :: *) (m :: * -> *) (a :: *) where
  typeRep# :: proxy a -> TypeRep s m

instance {-# OVERLAPPABLE #-} T.Typeable a => HasTypeRep s m a where
  typeRep# proxy = TypeRep (T.typeRep proxy)

instance {-# OVERLAPPABLE #-} HasTypeRep s m a => HasTypeRep s m (m a) where
  typeRep# _ = TypeRep $
    let ty = (typeRep# :: proxy a -> TypeRep s m) Proxy
    in T.mkTyConApp (T.mkTyCon3 "" "" ":monad:") [rawTypeRep ty]

instance (HasTypeRep s m a, HasTypeRep s m b) => HasTypeRep s m (a -> b) where
  typeRep# _ = TypeRep $
    let tyA = (typeRep# :: proxy a -> TypeRep s m) Proxy
        tyB = (typeRep# :: proxy b -> TypeRep s m) Proxy
    in T.mkFunTy (rawTypeRep tyA) (rawTypeRep tyB)

instance {-# INCOHERENT #-} HasTypeRep s m s where
  typeRep# _ = stateTypeRep

-- | A concrete representation of a type of some expression, with a
-- state type @s@ and monad type @m@.
data TypeRep (s :: *) (m :: * -> *) where
  TypeRep :: T.TypeRep -> TypeRep s m
  deriving Eq

instance Show (TypeRep s m) where
  show = show . rawTypeRep

-- | The 'TypeRep' of the state variable.
stateTypeRep :: TypeRep s m
stateTypeRep = TypeRep $ T.mkTyConApp (T.mkTyCon3 "" "" ":state:") []

-- | Get the underlying 'T.TypeRep' from a 'TypeRep'.
rawTypeRep :: TypeRep s m -> T.TypeRep
rawTypeRep (TypeRep ty) = ty

-- | Takes a value of type @a@ with state @s@ in some monad @m@, and
-- returns a concrete representation of that type.
typeRep :: forall s m a proxy. HasTypeRep s m a => proxy a -> TypeRep s m
typeRep = typeRep#

-- | Get the type of a value.
typeOf :: forall s m a. HasTypeRep s m a => a -> TypeRep s m
typeOf _ = typeRep @s @m @a Proxy

-- | The type-safe cast operation.
cast :: forall s m a b. (HasTypeRep s m a, HasTypeRep s m b) => a -> Maybe b
cast x = if typeRep @s @m @a Proxy == typeRep @s @m @b Proxy
         then Just $ unsafeCoerce x
         else Nothing

-- | Extract a witness of equality of two types
eqT :: forall s m a b. (HasTypeRep s m a, HasTypeRep s m b) => Maybe (a :~: b)
eqT = if typeRep @s @m @a Proxy == typeRep @s @m @b Proxy
      then Just $ unsafeCoerce Refl
      else Nothing

-- | Cast through a type constructor.
gcast :: forall s m a b c. (HasTypeRep s m a, HasTypeRep s m b) => c a -> Maybe (c b)
gcast x = fmap (\Refl -> x) (eqT @s @m @a @b)

-- | Applies a type to a given function type, if the types match.
funResultTy :: TypeRep s m -> TypeRep s m -> Maybe (TypeRep s m)
funResultTy t1 t2 = TypeRep <$> rawTypeRep t1 `T.funResultTy` rawTypeRep t2

-- | The arity of a type. Non-function types have an arity of 0.
typeArity :: TypeRep s m -> Int
typeArity = go . rawTypeRep where
  go ty = case T.splitTyConApp ty of
    (con, [_, resultType]) | con == funTyCon -> 1 + go resultType
    _ -> 0

  funTyCon = T.typeRepTyCon (T.typeRep @Proxy @(() -> ()) Proxy)
