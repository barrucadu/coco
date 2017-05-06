{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Test.CoCo.TypeInfo
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ScopedTypeVariables, TemplateHaskell
--
-- Information about types.
module Test.CoCo.TypeInfo where

import Control.Monad (forM)
import Data.Char (isAlpha, toLower)
import Data.Proxy (Proxy(..))
import qualified Data.Typeable as T
import Language.Haskell.TH.Syntax (Exp(..), Type(..))
import Test.LeanCheck (Listable, list)

import Test.CoCo.Type (Dynamic, unsafeToDyn)
import Test.CoCo.Util

-- | Information about a type.
data TypeInfo = TypeInfo
  { listValues :: [Dynamic]
    -- ^ Produce a (possibly infinite) list of values of this type.
  , varName    :: Char
  -- ^ Base name for variables of this type. Conflicting names will be
  -- made distinct with a numeric suffix.
  }

-- | Produce a base name for a variable from a type.
--
-- Returns @'z'@ if the type is not in the list.
getVariableBaseName :: [(T.TypeRep, TypeInfo)] -> T.TypeRep -> Char
getVariableBaseName typeInfos ty = maybe 'z' varName (lookup ty typeInfos)

-- | Get values of a type.
--
-- Returns @[]@ if the type is not in the list.
getTypeValues :: [(T.TypeRep, TypeInfo)] -> T.TypeRep -> [Dynamic]
getTypeValues typeInfos ty = maybe [] listValues (lookup ty typeInfos)

-- | 'TypeInfo' for @()@, @Bool@, @Char@, @Double@, @Float@, @Int@,
-- @Integer@ and @Ordering@; and @[a]@, @Maybe a@, @Either a b@,
-- @(a,b)@, and @(a,b,c)@ where all type variables are concrete in the
-- first list.
defaultTypeInfos :: [(T.TypeRep, TypeInfo)]
defaultTypeInfos =
  $(do c0s <- map constr <$> sequence [[t|()|], [t|Bool|], [t|Char|], [t|Double|], [t|Float|], [t|Int|], [t|Integer|], [t|Ordering|]]
       c1s <- map constr <$> sequence [[t|[()]|], [t|Maybe()|]]
       c2s <- map constr <$> sequence [[t|Either()()|], [t|((),())|]]
       c3s <- map constr <$> sequence [[t|((),(),())|]]
       let mkapps = map (foldl1 AppT) . sequence
       let types = c0s ++ mkapps [c1s, c0s] ++ mkapps [c2s, c0s, c0s] ++ mkapps [c3s, c0s, c0s, c0s]
       infos <- forM types (\ty -> [|makeTypeInfo (Proxy :: Proxy $(pure ty))|])
       pure (ListE infos)
   )

-- | Make the 'TypeInfo' for a listable type.
makeTypeInfo :: (Listable a, T.Typeable a) => proxy a -> (T.TypeRep, TypeInfo)
makeTypeInfo p = (T.typeRep p, TypeInfo { listValues = dynamicListValues p, varName = variableName p })

-- | Produce dynamic values from a 'Listable' instance.
dynamicListValues :: forall a proxy. (Listable a, T.Typeable a) => proxy a -> [Dynamic]
dynamicListValues p = map (unsafeToDyn $ T.typeRep p) (list :: [a])

-- | Like 'dynamicListValues' but takes an actual value, not a proxy.
dynamicListValues' :: forall a. (Listable a, T.Typeable a) => a -> [Dynamic]
dynamicListValues' _ = dynamicListValues (Proxy :: Proxy a)

-- | Produce a variable name from a type. This is mostly just @show@
-- of the 'T.TypeRep', but with some special cases.
variableName :: forall a proxy. T.Typeable a => proxy a -> Char
variableName p
    | tyrep `elem` intTypes   = 'x'
    | tyrep `elem` floatTypes = 'd'
    | otherwise = defname
  where
    tyrep = T.typeRep p

    -- groups of types
    intTypes   = [T.typeOf (undefined::Int), T.typeOf (undefined::Integer)]
    floatTypes = [T.typeOf (undefined::Double), T.typeOf (undefined::Float)]

    -- default name is the first alpha character in the @show@ of the
    -- typerep, or "a" if there are none.
    defname = case filter isAlpha (show tyrep) of
      (c:_) -> toLower c
      []    -> 'a'

-- | Like 'variableName' but takes an actual value, not a proxy.
variableName' :: forall a. T.Typeable a => a -> Char
variableName' _ = variableName (Proxy :: Proxy a)
