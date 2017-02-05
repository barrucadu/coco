{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Test.Spec.Concurrency
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ScopedTypeVariables, TemplateHaskell
--
-- List values of a type.
module Test.Spec.List where

import Control.Monad (forM)
import Data.Proxy (Proxy(..))
import qualified Data.Typeable as T
import Data.Void (Void)
import Language.Haskell.TH.Syntax (Exp(..), Guard(..), Type(..))
import Test.LeanCheck (Listable, list)

import Test.Spec.Type (Dynamic, TypeRep, unsafeToDyn, rawTypeRep)
import Test.Spec.Util

-- | List values of types @()@, @Bool@, @Char@, @Double@, @Float@,
-- @Int@, @Integer@ and @Ordering@; and @[a]@, @Maybe a@, @Either a
-- b@, @(a,b)@, and @(a,b,c)@ where all type variables are concrete in
-- the first list.
defaultListValues :: TypeRep Void Void1 -> [Dynamic Void Void1]
defaultListValues = defaultListValues' . rawTypeRep

-- | Like 'defaultListValues' but takes a normal 'T.TypeRep'.
defaultListValues' :: T.TypeRep -> [Dynamic Void Void1]
defaultListValues' ty0 =
  $(do c0s <- map constr <$> sequence [[t|()|], [t|Bool|], [t|Char|], [t|Double|], [t|Float|], [t|Int|], [t|Integer|], [t|Ordering|]]
       c1s <- map constr <$> sequence [[t|[()]|], [t|Maybe()|]]
       c2s <- map constr <$> sequence [[t|Either()()|], [t|((),())|]]
       c3s <- map constr <$> sequence [[t|((),(),())|]]
       let mkapps = map (foldl1 AppT) . sequence
       let cases = c0s ++ mkapps [c1s, c0s] ++ mkapps [c2s, c0s, c0s] ++ mkapps [c3s, c0s, c0s, c0s]
       qcases <- forM cases (\ty ->
         let p = [|Proxy :: Proxy $(pure ty)|]
             g = [|ty0 == T.typeRep  $p|]
             e = [|dynamicListValues $p|]
         in (\g' e' -> (NormalG g', e')) <$> g <*> e)
       oth <- [|otherwise|]
       pure . MultiIfE $ qcases ++ [(NormalG oth, ListE [])]
   )

-- | Produce dynamic values from a 'Listable' instance.
dynamicListValues :: forall a proxy. (Listable a, T.Typeable a) => proxy a -> [Dynamic Void Void1]
dynamicListValues p = map (unsafeToDyn $ T.typeRep p) (list :: [a])

-- | Like 'dynamicListValues' but takes an actual value, not a proxy.
dynamicListValues' :: forall a. (Listable a, T.Typeable a) => a -> [Dynamic Void Void1]
dynamicListValues' _ = dynamicListValues (Proxy :: Proxy a)
