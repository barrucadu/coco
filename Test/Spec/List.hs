{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Test.Spec.Concurrency
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ScopedTypeVariables
--
-- List values of a type.
module Test.Spec.List where

import Data.Proxy (Proxy(..))
import qualified Data.Typeable as T
import Test.LeanCheck (Listable, list)

import Test.Spec.Type (Dynamic, TypeRep, possiblyUnsafeToDyn, rawTypeRep)

-- | List values of types @()@, @Char@, @Double@, @Float@, @Int@,
-- @Integer@ and @Ordering@; and [a]@, @Maybe a@, @Either a b@, and
-- @(a,b)@, where all type variables are concrete in the first list.
defaultListValues :: TypeRep s m -> [Dynamic s m]
defaultListValues = defaultListValues' . rawTypeRep

-- | Like 'defaultListValues' but takes a normal 'T.TypeRep'.
defaultListValues' :: T.TypeRep -> [Dynamic s m]
defaultListValues' ty
  | ty == T.typeRep (Proxy :: Proxy ())       = dynamicListValues (Proxy :: Proxy ())
  | ty == T.typeRep (Proxy :: Proxy Char)     = dynamicListValues (Proxy :: Proxy Char)
  | ty == T.typeRep (Proxy :: Proxy Double)   = dynamicListValues (Proxy :: Proxy Double)
  | ty == T.typeRep (Proxy :: Proxy Float)    = dynamicListValues (Proxy :: Proxy Float)
  | ty == T.typeRep (Proxy :: Proxy Int)      = dynamicListValues (Proxy :: Proxy Int)
  | ty == T.typeRep (Proxy :: Proxy Integer)  = dynamicListValues (Proxy :: Proxy Integer)
  | ty == T.typeRep (Proxy :: Proxy Ordering) = dynamicListValues (Proxy :: Proxy Ordering)
  | ty == T.typeRep (Proxy :: Proxy [()])       = dynamicListValues (Proxy :: Proxy [()])
  | ty == T.typeRep (Proxy :: Proxy [Char])     = dynamicListValues (Proxy :: Proxy [Char])
  | ty == T.typeRep (Proxy :: Proxy [Double])   = dynamicListValues (Proxy :: Proxy [Double])
  | ty == T.typeRep (Proxy :: Proxy [Float])    = dynamicListValues (Proxy :: Proxy [Float])
  | ty == T.typeRep (Proxy :: Proxy [Int])      = dynamicListValues (Proxy :: Proxy [Int])
  | ty == T.typeRep (Proxy :: Proxy [Integer])  = dynamicListValues (Proxy :: Proxy [Integer])
  | ty == T.typeRep (Proxy :: Proxy [Ordering]) = dynamicListValues (Proxy :: Proxy [Ordering])
  | ty == T.typeRep (Proxy :: Proxy (Maybe ()))       = dynamicListValues (Proxy :: Proxy (Maybe ()))
  | ty == T.typeRep (Proxy :: Proxy (Maybe Char))     = dynamicListValues (Proxy :: Proxy (Maybe Char))
  | ty == T.typeRep (Proxy :: Proxy (Maybe Double))   = dynamicListValues (Proxy :: Proxy (Maybe Double))
  | ty == T.typeRep (Proxy :: Proxy (Maybe Float))    = dynamicListValues (Proxy :: Proxy (Maybe Float))
  | ty == T.typeRep (Proxy :: Proxy (Maybe Int))      = dynamicListValues (Proxy :: Proxy (Maybe Int))
  | ty == T.typeRep (Proxy :: Proxy (Maybe Integer))  = dynamicListValues (Proxy :: Proxy (Maybe Integer))
  | ty == T.typeRep (Proxy :: Proxy (Maybe Ordering)) = dynamicListValues (Proxy :: Proxy (Maybe Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either () ()))       = dynamicListValues (Proxy :: Proxy (Either () ()))
  | ty == T.typeRep (Proxy :: Proxy (Either () Char))     = dynamicListValues (Proxy :: Proxy (Either () Char))
  | ty == T.typeRep (Proxy :: Proxy (Either () Double))   = dynamicListValues (Proxy :: Proxy (Either () Double))
  | ty == T.typeRep (Proxy :: Proxy (Either () Float))    = dynamicListValues (Proxy :: Proxy (Either () Float))
  | ty == T.typeRep (Proxy :: Proxy (Either () Int))      = dynamicListValues (Proxy :: Proxy (Either () Int))
  | ty == T.typeRep (Proxy :: Proxy (Either () Integer))  = dynamicListValues (Proxy :: Proxy (Either () Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either () Ordering)) = dynamicListValues (Proxy :: Proxy (Either () Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either Char ()))       = dynamicListValues (Proxy :: Proxy (Either Char ()))
  | ty == T.typeRep (Proxy :: Proxy (Either Char Char))     = dynamicListValues (Proxy :: Proxy (Either Char Char))
  | ty == T.typeRep (Proxy :: Proxy (Either Char Double))   = dynamicListValues (Proxy :: Proxy (Either Char Double))
  | ty == T.typeRep (Proxy :: Proxy (Either Char Float))    = dynamicListValues (Proxy :: Proxy (Either Char Float))
  | ty == T.typeRep (Proxy :: Proxy (Either Char Int))      = dynamicListValues (Proxy :: Proxy (Either Char Int))
  | ty == T.typeRep (Proxy :: Proxy (Either Char Integer))  = dynamicListValues (Proxy :: Proxy (Either Char Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either Char Ordering)) = dynamicListValues (Proxy :: Proxy (Either Char Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either Double ()))       = dynamicListValues (Proxy :: Proxy (Either Double ()))
  | ty == T.typeRep (Proxy :: Proxy (Either Double Char))     = dynamicListValues (Proxy :: Proxy (Either Double Char))
  | ty == T.typeRep (Proxy :: Proxy (Either Double Double))   = dynamicListValues (Proxy :: Proxy (Either Double Double))
  | ty == T.typeRep (Proxy :: Proxy (Either Double Float))    = dynamicListValues (Proxy :: Proxy (Either Double Float))
  | ty == T.typeRep (Proxy :: Proxy (Either Double Int))      = dynamicListValues (Proxy :: Proxy (Either Double Int))
  | ty == T.typeRep (Proxy :: Proxy (Either Double Integer))  = dynamicListValues (Proxy :: Proxy (Either Double Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either Double Ordering)) = dynamicListValues (Proxy :: Proxy (Either Double Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either Float ()))       = dynamicListValues (Proxy :: Proxy (Either Float ()))
  | ty == T.typeRep (Proxy :: Proxy (Either Float Char))     = dynamicListValues (Proxy :: Proxy (Either Float Char))
  | ty == T.typeRep (Proxy :: Proxy (Either Float Double))   = dynamicListValues (Proxy :: Proxy (Either Float Double))
  | ty == T.typeRep (Proxy :: Proxy (Either Float Float))    = dynamicListValues (Proxy :: Proxy (Either Float Float))
  | ty == T.typeRep (Proxy :: Proxy (Either Float Int))      = dynamicListValues (Proxy :: Proxy (Either Float Int))
  | ty == T.typeRep (Proxy :: Proxy (Either Float Integer))  = dynamicListValues (Proxy :: Proxy (Either Float Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either Float Ordering)) = dynamicListValues (Proxy :: Proxy (Either Float Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either Int ()))       = dynamicListValues (Proxy :: Proxy (Either Int ()))
  | ty == T.typeRep (Proxy :: Proxy (Either Int Char))     = dynamicListValues (Proxy :: Proxy (Either Int Char))
  | ty == T.typeRep (Proxy :: Proxy (Either Int Double))   = dynamicListValues (Proxy :: Proxy (Either Int Double))
  | ty == T.typeRep (Proxy :: Proxy (Either Int Float))    = dynamicListValues (Proxy :: Proxy (Either Int Float))
  | ty == T.typeRep (Proxy :: Proxy (Either Int Int))      = dynamicListValues (Proxy :: Proxy (Either Int Int))
  | ty == T.typeRep (Proxy :: Proxy (Either Int Integer))  = dynamicListValues (Proxy :: Proxy (Either Int Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either Int Ordering)) = dynamicListValues (Proxy :: Proxy (Either Int Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer ()))       = dynamicListValues (Proxy :: Proxy (Either Integer ()))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer Char))     = dynamicListValues (Proxy :: Proxy (Either Integer Char))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer Double))   = dynamicListValues (Proxy :: Proxy (Either Integer Double))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer Float))    = dynamicListValues (Proxy :: Proxy (Either Integer Float))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer Int))      = dynamicListValues (Proxy :: Proxy (Either Integer Int))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer Integer))  = dynamicListValues (Proxy :: Proxy (Either Integer Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either Integer Ordering)) = dynamicListValues (Proxy :: Proxy (Either Integer Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering ()))       = dynamicListValues (Proxy :: Proxy (Either Ordering ()))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering Char))     = dynamicListValues (Proxy :: Proxy (Either Ordering Char))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering Double))   = dynamicListValues (Proxy :: Proxy (Either Ordering Double))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering Float))    = dynamicListValues (Proxy :: Proxy (Either Ordering Float))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering Int))      = dynamicListValues (Proxy :: Proxy (Either Ordering Int))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering Integer))  = dynamicListValues (Proxy :: Proxy (Either Ordering Integer))
  | ty == T.typeRep (Proxy :: Proxy (Either Ordering Ordering)) = dynamicListValues (Proxy :: Proxy (Either Ordering Ordering))
  | ty == T.typeRep (Proxy :: Proxy ((), ()))       = dynamicListValues (Proxy :: Proxy ((), ()))
  | ty == T.typeRep (Proxy :: Proxy ((), Char))     = dynamicListValues (Proxy :: Proxy ((), Char))
  | ty == T.typeRep (Proxy :: Proxy ((), Double))   = dynamicListValues (Proxy :: Proxy ((), Double))
  | ty == T.typeRep (Proxy :: Proxy ((), Float))    = dynamicListValues (Proxy :: Proxy ((), Float))
  | ty == T.typeRep (Proxy :: Proxy ((), Int))      = dynamicListValues (Proxy :: Proxy ((), Int))
  | ty == T.typeRep (Proxy :: Proxy ((), Integer))  = dynamicListValues (Proxy :: Proxy ((), Integer))
  | ty == T.typeRep (Proxy :: Proxy ((), Ordering)) = dynamicListValues (Proxy :: Proxy ((), Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Char, ()))       = dynamicListValues (Proxy :: Proxy (Char, ()))
  | ty == T.typeRep (Proxy :: Proxy (Char, Char))     = dynamicListValues (Proxy :: Proxy (Char, Char))
  | ty == T.typeRep (Proxy :: Proxy (Char, Double))   = dynamicListValues (Proxy :: Proxy (Char, Double))
  | ty == T.typeRep (Proxy :: Proxy (Char, Float))    = dynamicListValues (Proxy :: Proxy (Char, Float))
  | ty == T.typeRep (Proxy :: Proxy (Char, Int))      = dynamicListValues (Proxy :: Proxy (Char, Int))
  | ty == T.typeRep (Proxy :: Proxy (Char, Integer))  = dynamicListValues (Proxy :: Proxy (Char, Integer))
  | ty == T.typeRep (Proxy :: Proxy (Char, Ordering)) = dynamicListValues (Proxy :: Proxy (Char, Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Double, ()))       = dynamicListValues (Proxy :: Proxy (Double, ()))
  | ty == T.typeRep (Proxy :: Proxy (Double, Char))     = dynamicListValues (Proxy :: Proxy (Double, Char))
  | ty == T.typeRep (Proxy :: Proxy (Double, Double))   = dynamicListValues (Proxy :: Proxy (Double, Double))
  | ty == T.typeRep (Proxy :: Proxy (Double, Float))    = dynamicListValues (Proxy :: Proxy (Double, Float))
  | ty == T.typeRep (Proxy :: Proxy (Double, Int))      = dynamicListValues (Proxy :: Proxy (Double, Int))
  | ty == T.typeRep (Proxy :: Proxy (Double, Integer))  = dynamicListValues (Proxy :: Proxy (Double, Integer))
  | ty == T.typeRep (Proxy :: Proxy (Double, Ordering)) = dynamicListValues (Proxy :: Proxy (Double, Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Float, ()))       = dynamicListValues (Proxy :: Proxy (Float, ()))
  | ty == T.typeRep (Proxy :: Proxy (Float, Char))     = dynamicListValues (Proxy :: Proxy (Float, Char))
  | ty == T.typeRep (Proxy :: Proxy (Float, Double))   = dynamicListValues (Proxy :: Proxy (Float, Double))
  | ty == T.typeRep (Proxy :: Proxy (Float, Float))    = dynamicListValues (Proxy :: Proxy (Float, Float))
  | ty == T.typeRep (Proxy :: Proxy (Float, Int))      = dynamicListValues (Proxy :: Proxy (Float, Int))
  | ty == T.typeRep (Proxy :: Proxy (Float, Integer))  = dynamicListValues (Proxy :: Proxy (Float, Integer))
  | ty == T.typeRep (Proxy :: Proxy (Float, Ordering)) = dynamicListValues (Proxy :: Proxy (Float, Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Int, ()))       = dynamicListValues (Proxy :: Proxy (Int, ()))
  | ty == T.typeRep (Proxy :: Proxy (Int, Char))     = dynamicListValues (Proxy :: Proxy (Int, Char))
  | ty == T.typeRep (Proxy :: Proxy (Int, Double))   = dynamicListValues (Proxy :: Proxy (Int, Double))
  | ty == T.typeRep (Proxy :: Proxy (Int, Float))    = dynamicListValues (Proxy :: Proxy (Int, Float))
  | ty == T.typeRep (Proxy :: Proxy (Int, Int))      = dynamicListValues (Proxy :: Proxy (Int, Int))
  | ty == T.typeRep (Proxy :: Proxy (Int, Integer))  = dynamicListValues (Proxy :: Proxy (Int, Integer))
  | ty == T.typeRep (Proxy :: Proxy (Int, Ordering)) = dynamicListValues (Proxy :: Proxy (Int, Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Integer, ()))       = dynamicListValues (Proxy :: Proxy (Integer, ()))
  | ty == T.typeRep (Proxy :: Proxy (Integer, Char))     = dynamicListValues (Proxy :: Proxy (Integer, Char))
  | ty == T.typeRep (Proxy :: Proxy (Integer, Double))   = dynamicListValues (Proxy :: Proxy (Integer, Double))
  | ty == T.typeRep (Proxy :: Proxy (Integer, Float))    = dynamicListValues (Proxy :: Proxy (Integer, Float))
  | ty == T.typeRep (Proxy :: Proxy (Integer, Int))      = dynamicListValues (Proxy :: Proxy (Integer, Int))
  | ty == T.typeRep (Proxy :: Proxy (Integer, Integer))  = dynamicListValues (Proxy :: Proxy (Integer, Integer))
  | ty == T.typeRep (Proxy :: Proxy (Integer, Ordering)) = dynamicListValues (Proxy :: Proxy (Integer, Ordering))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, ()))       = dynamicListValues (Proxy :: Proxy (Ordering, ()))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, Char))     = dynamicListValues (Proxy :: Proxy (Ordering, Char))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, Double))   = dynamicListValues (Proxy :: Proxy (Ordering, Double))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, Float))    = dynamicListValues (Proxy :: Proxy (Ordering, Float))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, Int))      = dynamicListValues (Proxy :: Proxy (Ordering, Int))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, Integer))  = dynamicListValues (Proxy :: Proxy (Ordering, Integer))
  | ty == T.typeRep (Proxy :: Proxy (Ordering, Ordering)) = dynamicListValues (Proxy :: Proxy (Ordering, Ordering))
  | otherwise = []

-- | Produce dynamic values from a 'Listable' instance.
dynamicListValues :: forall s m a proxy. (Listable a, T.Typeable a) => proxy a -> [Dynamic s m]
dynamicListValues p = map (possiblyUnsafeToDyn $ T.typeRep p) (list :: [a])

-- | Like 'dynamicListValues' but takes an actual value, not a proxy.
dynamicListValues' :: forall s m a. (Listable a, T.Typeable a) => a -> [Dynamic s m]
dynamicListValues' _ = dynamicListValues (Proxy :: Proxy a)
