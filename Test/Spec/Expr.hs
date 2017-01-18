-- |
-- Module      : Test.Spec.Expr
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- Constructing and evaluating dynamically-typed expressions.
module Test.Spec.Expr
  ( -- * Expressions
    Expr
  , constant
  , showConstant
  , variable
  , ($$)
  , constants
  , variables
  , assign
  , evaluate
  , evaluateDyn
  -- * Types
  , exprTypeArity
  , exprTypeRep
  ) where

import Data.Char (isAlphaNum)
import Data.Dynamic (Dynamic, dynApply, dynTypeRep, fromDynamic, toDyn)
import Data.Function (on)
import Data.List (intercalate, nubBy)
import Data.Typeable (Typeable, TypeRep, funResultTy, typeRep)

import Test.Spec.Type

-------------------------------------------------------------------------------
-- Expressions

-- | An expression.
data Expr
  = Constant String Dynamic
  -- ^ A dynamically-typed constant.
  | Variable String TypeRep
  -- ^ A named variable of a given type.
  | FunAp Expr Expr TypeRep
  -- ^ A function application. It's important that we don't expose
  -- this constructor, so the correctness of the 'TypeRep' can be
  -- ensured.

instance Show Expr where
  show = go True where
    go _ (Constant s _) = toPrefix s
    go _ (Variable s _) = toPrefix s
    go b ap =
      let inner = intercalate " " $ case unfoldAp ap of
            [(Constant s _), arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            [(Variable s _), arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            unfolded -> map (go False) unfolded
      in if b then inner else "(" ++ inner ++ ")"

    toPrefix s
      | not (isSymbolic s) = s
      | otherwise = "(" ++ s ++ ")"

    unfoldAp (FunAp f e _) = unfoldAp f ++ [e]
    unfoldAp e = [e]

    isSymbolic = not . all isAlphaNum

-- | A constant value.
constant :: Typeable a => String -> a -> Expr
constant s = Constant s . toDyn

-- | A constant value from a type which can be shown.
showConstant :: (Show a, Typeable a) => a -> Expr
showConstant a = constant (show a) a

-- | A variable.
variable :: Typeable a => String -> proxy a -> Expr
variable s = Variable s . typeRep

-- | Apply a function, if well-typed.
($$) :: Expr -> Expr -> Maybe Expr
f $$ e = FunAp f e <$> (exprTypeRep f `funResultTy` exprTypeRep e)

-- | Get all constants in an expression, without repetition.
constants :: Expr -> [(String, Dynamic)]
constants = nubBy ((==) `on` fst) . go where
  go (Constant s dyn) = [(s, dyn)]
  go (Variable _ _) = []
  go (FunAp f e _) = go f ++ go e

-- | Get all variables in an expression, without repetition.
variables :: Expr -> [(String, TypeRep)]
variables = nubBy ((==) `on` fst) . go where
  go (Constant _ _) = []
  go (Variable s ty) = [(s, ty)]
  go (FunAp f e _) = variables f ++ variables e

-- | Plug in a value for all occurrences of a variable, if the types
-- match.
assign :: String
       -- ^ The name of the variable.
       -> Expr
       -- ^ the new value.
       -> Expr
       -- ^ The expression being modified
       -> Maybe Expr
assign _ _ o@(Constant _ _) = Just o
assign s v o@(Variable s2 ty)
  | s == s2 = if exprTypeRep v == ty then Just v else Nothing
  | otherwise = Just o
assign s v (FunAp f e ty) = FunAp <$> assign s v f <*> assign s v e <*> Just ty

-- | Evaluate an expression, if it has no free variables and is the
-- correct type.
evaluate :: Typeable a => Expr -> Maybe a
evaluate e = fromDynamic =<< evaluateDyn e

-- | Evaluate an expression, if it has no free variables.
evaluateDyn :: Expr -> Maybe Dynamic
evaluateDyn (Constant _ dyn) = Just dyn
evaluateDyn (Variable _ _)   = Nothing
evaluateDyn (FunAp f e _)    = do
  f' <- evaluateDyn f
  e' <- evaluateDyn e
  f' `dynApply` e'


-------------------------------------------------------------------------------
-- Types

-- | Get the arity of an expression. Non-function types have an arity
-- of 0.
exprTypeArity :: Expr -> Int
exprTypeArity = typeArity . exprTypeRep

-- | Get the type of an expression.
exprTypeRep :: Expr -> TypeRep
exprTypeRep (Constant _ dyn) = dynTypeRep dyn
exprTypeRep (Variable _ ty)  = ty
exprTypeRep (FunAp _ _ ty) = ty
