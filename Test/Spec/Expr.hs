{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      : Test.Spec.Expr
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs, ScopedTypeVariables, TypeApplications
--
-- Constructing and evaluating dynamically-typed monadic expressions.
--
-- @
-- > :{
-- let ioplus = constant \@(MVar Int) \@IO \@(MVar Int -> Int -> IO ()) "io+" (\v a -> modifyMVar_ v (\x -> pure $ x+a))
-- let five   = showConstant (5::Int)
-- mvar <- newMVar (5::Int)
-- case evaluate \@(MVar Int) \@IO \@(IO ()) mvar . fromJust $ fromJust (ioplus $$ stateVariable) $$ five of
--   Just act -> act
--   Nothing  -> pure ()
-- readMVar mvar
-- :}
-- 10
-- @
--
-- As you can see, there is basically no type inference working at the
-- moment. I hope that this will improve as I build more on top.
module Test.Spec.Expr
  ( -- * Expressions
    Expr
  , constant
  , showConstant
  , variable
  , stateVariable
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
import Data.Function (on)
import Data.List (intercalate, nub, nubBy)

import Test.Spec.Type

-------------------------------------------------------------------------------
-- Expressions

-- | An expression with effects in some monad @m@.
data Expr s m where
  -- It's important that these constructors aren't exposed, so the
  -- correctness of the 'TypeRep's can be ensured.
  Constant :: String -> Dynamic s m -> Expr s m
  Variable :: String -> TypeRep s m -> Expr s m
  StateVar :: Expr s m
  FunAp    :: Expr s m -> Expr s m -> TypeRep s m -> Expr s m

instance Show (Expr s m) where
  show = go True where
    go _ (Constant s _) = toPrefix s
    go _ (Variable s _) = toPrefix s
    go _ StateVar = ":state:"
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
constant :: HasTypeRep s m a => String -> a -> Expr s m
constant s a = Constant s (toDyn a)

-- | A constant value from a type which can be shown.
showConstant :: (Show a, HasTypeRep s m a) => a -> Expr s m
showConstant a = constant (show a) a

-- | A variable.
variable :: HasTypeRep s m a => String -> proxy a -> Expr s m
variable s = Variable s . typeRep

-- | The state variable
stateVariable :: Expr s m
stateVariable = StateVar

-- | Apply a function, if well-typed.
($$) :: Expr s m -> Expr s m -> Maybe (Expr s m)
f $$ e = FunAp f e <$> (exprTypeRep f `funResultTy` exprTypeRep e)

-- | Get all constants in an expression, without repetition.
constants :: Expr s m -> [(String, Dynamic s m)]
constants = nubBy ((==) `on` fst) . go where
  go (Constant s dyn) = [(s, dyn)]
  go (FunAp f e _) = go f ++ go e
  go _ = []

-- | Get all variables in an expression, without repetition.
variables :: Expr s m -> [(String, TypeRep s m)]
variables = nub . go where
  go (Variable s ty) = [(s, ty)]
  go (FunAp f e _) = variables f ++ variables e
  go _ = []

-- | Plug in a value for all occurrences of a variable, if the types
-- match.
assign :: String
       -- ^ The name of the variable.
       -> Expr s m
       -- ^ the new value.
       -> Expr s m
       -- ^ The expression being modified
       -> Maybe (Expr s m)
assign s v e@(Variable s2 ty)
  | s == s2 = if exprTypeRep v == ty then Just v else Nothing
  | otherwise = Just e
assign s v (FunAp f e ty) = FunAp <$> assign s v f <*> assign s v e <*> Just ty
assign _ _ e = Just e

-- | Evaluate an expression, if it has no free variables and it is the
-- correct type.
evaluate :: forall s m a. (Monad m, HasTypeRep s m a) => s -> Expr s m -> Maybe a
evaluate s e = fromDyn @s @m @a =<< evaluateDyn s e

-- | Evaluate an expression, if it has no free variables.
evaluateDyn :: forall s m. Monad m => s -> Expr s m -> Maybe (Dynamic s m)
evaluateDyn s = go where
  go StateVar = Just (toDyn @s @m @s s)
  go (Constant _ dyn) = Just dyn
  go (Variable _ _) = Nothing
  go (FunAp f e _) = do
    f' <- go f
    e' <- go e
    case f' `dynApp` e' of
      Just x  -> Just x
      -- this should never happen, as '$$' checks the application is
      -- type-correct.
      Nothing -> error ("can't apply function " ++ show f' ++ " to argument " ++ show e')

-------------------------------------------------------------------------------
-- Types

-- | Get the arity of an expression. Non-function types have an arity
-- of 0.
exprTypeArity :: Expr s m -> Int
exprTypeArity = typeArity . exprTypeRep

-- | Get the type of an expression.
exprTypeRep :: Expr s m -> TypeRep s m
exprTypeRep (Constant _ dyn)  = dynTypeRep dyn
exprTypeRep (Variable _   ty) = ty
exprTypeRep (FunAp    _ _ ty) = ty
exprTypeRep StateVar          = stateTypeRep
