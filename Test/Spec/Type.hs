-- |
-- Module      : Test.Spec.Type
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- Extra functions and utilities for dealing with types.
module Test.Spec.Type where

import Data.Proxy (Proxy(..))
import Data.Typeable

-------------------------------------------------------------------------------
-- * 'TyCon's

-- | The function arrow.
funTyCon :: TyCon
funTyCon = tyCon (Proxy :: Proxy (() -> ()))

-- | The constructor of a type.
tyCon :: Typeable a => proxy a -> TyCon
tyCon = typeRepTyCon . typeRep


-------------------------------------------------------------------------------
-- * 'TypeRep's

-- | The arity of a type. Non-function types have an arity of 0.
typeArity :: TypeRep -> Int
typeArity ty = case splitTyConApp ty of
  (con, [_, resultType]) | con == funTyCon -> 1 + typeArity resultType
  _ -> 0
