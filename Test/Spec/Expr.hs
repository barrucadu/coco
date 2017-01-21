{-# LANGUAGE GADTs #-}

-- |
-- Module      : Test.Spec.Expr
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs
--
-- Constructing and evaluating dynamically-typed monadic expressions.
--
-- @
-- > mvar <- newMVar (5::Int)
-- > let ioplus = constant "io+" (\v a -> modifyMVar_ v (\x -> pure $ x + (a::Int))) :: Expr (MVar Int) IO
-- > let five   = showConstant (5::Int)
-- > let act = do { f \<- ioplus $$ stateVariable; evaluate =<< (f $$ five) } :: Maybe (MVar Int -\> IO (Maybe (IO ())))
-- > :{
-- case act of
--   Just f  -> fromMaybe (pure ()) =<< f mvar
--   Nothing -> pure ()
-- :}
-- > readMVar mvar
-- 10
-- @
--
-- @
-- > let intvar = variable "x" (Proxy :: Proxy Int)
-- > let iopure = constant "pure" (pure :: Int -> IO Int) :: Expr () IO
-- > let five   = constant "5" (5::Int) :: Expr () IO
-- > let act = do { pureX \<- iopure $$ intvar; iofive <- iopure $$ five; evaluate =<< bind "x" iofive pureX } :: Maybe (() -\> IO (Maybe (IO Int)))
-- > :{
-- case act of
--   Just f -> maybe (pure ()) (print=<<) =<< f ()
--   Nothing -> pure ()
-- :}
-- 5
-- @
--
-- @
-- > let intvar = variable "x" (Proxy :: Proxy Int)
-- > let five   = constant "5" (5::Int) :: Expr () IO
-- > let act = do { evaluate =\<< let_ "x" five intvar } :: Maybe (() -\> IO (Maybe Int))
-- > :{
-- case act of
--   Just f -> maybe (pure ()) print =<< f ()
--   Nothing -> pure ()
-- :}
-- 5
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
  , let_
  , bind
  , constants
  , variables
  , freeVariables
  , boundVariables
  , saturate
  , assign
  , evaluate
  , evaluateDyn
  , exprSize

  -- * Types
  , exprTypeArity
  , exprTypeRep
  ) where

import Control.Monad (filterM, guard)
import Data.Char (isAlphaNum)
import Data.Function (on)
import Data.List ((\\), foldl', nub, nubBy)
import Data.Maybe (fromMaybe)

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
  Bind     :: String -> Expr s m -> Expr s m -> TypeRep s m -> Expr s m
  Let      :: String -> Expr s m -> Expr s m -> TypeRep s m -> Expr s m

instance Show (Expr s m) where
  show = go True where
    go _ (Constant s _) = toPrefix s
    go _ (Variable s _) = toPrefix s
    go _ StateVar = ":state:"
    go b (Bind var binder body _) =
      let inner = unwords [go b binder, ">>=", '\\':var, "->", go b body]
      in if b then inner else "(" ++ inner ++ ")"
    go b (Let var binder body _) =
      let inner = unwords ["let", var, "=", go b binder, "in", go b body]
      in if b then inner else "(" ++ inner ++ ")"
    go b ap@(FunAp _ _ _) =
      let inner = unwords $ case unfoldAp ap of
            [Constant s _, arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            [Variable s _, arg1, arg2]
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
--
-- @exprSize (constant "foo" foo) == 1@
constant :: HasTypeRep s m a => String -> a -> Expr s m
constant s a = Constant s (toDyn a)

-- | A constant value from a type which can be shown.
--
-- @exprSize (showConstant foo) == 1@
showConstant :: (Show a, HasTypeRep s m a) => a -> Expr s m
showConstant a = constant (show a) a

-- | A variable.
--
-- @exprSize (variable "x" proxy) == 1@
variable :: HasTypeRep s m a => String -> proxy a -> Expr s m
variable s = Variable s . typeRep

-- | The state variable
--
-- @exprSize stateVariable == 1@
stateVariable :: Expr s m
stateVariable = StateVar

-- | Apply a function, if well-typed.
--
-- @fmap exprSize (e1 $$ e2) == Just (1 + exprSize e1 + exprSize e2)@
($$) :: Expr s m -> Expr s m -> Maybe (Expr s m)
f $$ e = FunAp f e <$> (exprTypeRep f `funResultTy` exprTypeRep e)

-- | Bind a monadic value to a variable name, if well typed.
--
-- @fmap exprSize (bind "x" e1 e2) == Just (1 + exprSize e1 + exprSize e2)@
bind :: String   -- ^ Variable name
     -> Expr s m -- ^ Expression to bind
     -> Expr s m -- ^ Expression to bind variable in
     -> Maybe (Expr s m)
bind var binder body = do
  _ <- unmonad (exprTypeRep body)
  let boundVars = filter ((==var) . fst) (freeVariables body)
  innerTy <- unmonad (exprTypeRep binder)
  guard $ all ((==innerTy) . snd) boundVars
  pure $ Bind var binder body (exprTypeRep body)

-- | Bind a value to a variable name, if well typed.
--
-- @fmap exprSize (let_ "x" e1 e2) == Just (1 + exprSize e1 + exprSize e2)@
let_ :: String   -- ^ Variable name
     -> Expr s m -- ^ Expression to bind
     -> Expr s m -- ^ Expression to bind variable in
     -> Maybe (Expr s m)
let_ var binder body = do
  let boundVars = filter ((==var) . fst) (freeVariables body)
  guard $ all ((==exprTypeRep binder) . snd) boundVars
  pure $ Let var binder body (exprTypeRep body)

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
  go (Bind _ e1 e2 _) = variables e1 ++ variables e2
  go (Let _ e1 e2 _) = variables e1 ++ variables e2
  go _ = []

-- | Get all free variables in an expression, without repetition.
freeVariables :: Expr s m -> [(String, TypeRep s m)]
freeVariables = nub . go where
  go (Variable s ty) = [(s, ty)]
  go (FunAp f e _) = variables f ++ variables e
  go (Bind s e1 e2 _) = variables e1 ++ filter ((/=s) . fst) (variables e2)
  go (Let s e1 e2 _) = variables e1 ++ filter ((/=s) . fst) (variables e2)
  go _ = []

-- | Get all the bound variables in an expression, without repetition.
boundVariables :: Expr s m -> [(String, TypeRep s m)]
boundVariables expr = variables expr \\ freeVariables expr

-- | If an expression represents an unsaturated function, introduce
-- new variables to saturate it. These variables are free in the
-- resultant expression.
--
-- @exprSize (saturate e) == exprSize e + typeArity (exprTypeRep e)@
saturate :: Expr s m -> Expr s m
saturate expr = foldl' ($$!) expr vars where
  -- the should never happen, as we've just constructed the list of
  -- variables from the needed types.
  e1 $$! e2 = fromMaybe (error "type error in 'saturate'") (e1 $$ e2)

  -- the variables introduced to saturate the application
  vars = zipWith Variable (take (length tys) varnames) tys

  -- the list ["a", "b", "ba", "c", "ca", ...], sans those which are
  -- already variables in the expression.
  varnames = filter (`notElem` takenVars) . tail $ filterM (const [False, True]) ['z','y'..'a']
  takenVars = map fst (variables expr)

  -- the types of the function arguments
  tys = funArgTys (exprTypeRep expr)

-- | Plug in a value for all occurrences of a variable, if the types
-- match. A 'bind' of a variable of the same name is actually
-- introducing a fresh variable, so upon encountering a binding with
-- the variable name, assignment stops.
--
-- @fmap exprSize (assign "x" e1 e2) == Just (exprSize e2 + numOccurrences * (exprSize e1 - 1))@
--
-- Because 'assign' has the potential to greatly increase the size of
-- the expression, 'let_' is generally better.
assign :: String
       -- ^ The name of the variable.
       -> Expr s m
       -- ^ The new value.
       -> Expr s m
       -- ^ The expression being modified
       -> Maybe (Expr s m)
assign s v e@(Variable s2 ty)
  | s == s2   = if exprTypeRep v == ty then Just v else Nothing
  | otherwise = Just e
assign s v (FunAp f e ty) = FunAp <$> assign s v f <*> assign s v e <*> pure ty
assign s v (Bind s2 e1 e2 ty)
  | s == s2   = Bind s2 <$> assign s v e1 <*> pure e2 <*> pure ty
  | otherwise = Bind s2 <$> assign s v e1 <*> assign s v e2 <*> pure ty
assign s v (Let s2 e1 e2 ty)
  | s == s2   = Let s2 <$> assign s v e1 <*> pure e2 <*> pure ty
  | otherwise = Let s2 <$> assign s v e1 <*> assign s v e2 <*> pure ty
assign _ _ e = Just e

-- | Evaluate an expression, if it has no free variables and it is the
-- correct type.
--
-- If the outer 'Maybe' is @Nothing@, there are free variables. If the
-- inner 'Maybe' is @Nothing@, the type is incorrect.
evaluate :: (Monad m, HasTypeRep s m a) => Expr s m -> Maybe (s -> m (Maybe a))
evaluate e = (\f -> fmap fromDyn . f) <$> evaluateDyn e

-- | Evaluate an expression, if it has no free variables.
evaluateDyn :: Monad m => Expr s m -> Maybe (s -> m (Dynamic s m))
evaluateDyn expr
    | null (freeVariables expr) = Just (go [] expr)
    | otherwise = Nothing
  where
    go _ StateVar s = pure (toDyn s)
    go _ (Constant _ dyn) _ = pure dyn
    go env (Variable var _) _ = case lookup var env of
      Just dyn -> pure dyn
      -- this should never happen, as 'evaluateDyn' first checks that
      -- there are no free variables before calling 'go'.
      Nothing  -> error ("unexpected free variable " ++ var ++ " in expression")
    go env (FunAp f e _) s = do
      f' <- go env f s
      e' <- go env e s
      case f' `dynApp` e' of
        Just r -> pure r
        -- this should never happen, as '$$' checks the application is
        -- type-correct.
        Nothing -> error ("can't apply function " ++ show f' ++ " to argument " ++ show e')
    go env (Bind var e1 e2 _) s = do
      e1' <- go env e1 s
      case dynMonadic e1' of
        Just mx -> do
          x <- mx
          go ((var, x):env) e2 s
        -- this should never happen, as 'bind' checks the application
        -- is type-correct.
        Nothing -> error ("can't bind non-monadic expression " ++ show e1' ++ " to variable " ++ var ++ " in body " ++ show e2)
    go env (Let var e1 e2 _) s = do
      e1' <- go env e1 s
      go ((var, e1'):env) e2 s

-- | Get the size of an expression.
exprSize :: Expr s m -> Int
exprSize (Constant _ _)   = 1
exprSize (Variable _ _)   = 1
exprSize (FunAp e1 e2 _)  = 1 + exprSize e1 + exprSize e2
exprSize (Bind _ e1 e2 _) = 1 + exprSize e1 + exprSize e2
exprSize (Let _ e1 e2 _)  = 1 + exprSize e1 + exprSize e2
exprSize StateVar = 1


-------------------------------------------------------------------------------
-- Types

-- | Get the arity of an expression. Non-function types have an arity
-- of 0.
exprTypeArity :: Expr s m -> Int
exprTypeArity = typeArity . exprTypeRep

-- | Get the type of an expression.
exprTypeRep :: Expr s m -> TypeRep s m
exprTypeRep (Constant _ dyn) = dynTypeRep dyn
exprTypeRep (Variable _ ty)  = ty
exprTypeRep (FunAp _ _ ty)   = ty
exprTypeRep (Bind _ _ _ ty)  = ty
exprTypeRep (Let _ _ _ ty)   = ty
exprTypeRep StateVar = stateTypeRep
