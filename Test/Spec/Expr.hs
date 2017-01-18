{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Test.Spec.Expr
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : GADTs, ScopedTypeVariables
--
-- Constructing and evaluating dynamically-typed monadic expressions.
--
-- @
-- > :{
-- runST $ do
--   let stateplus = statefun1 "s+" (\a v -> modifySTRef v (+a))
--   var <- newSTRef (5::Int)
--   case evaluate var =<< (stateplus $$ five) of
--     Just act -> act
--     Nothing  -> pure ()
--   readSTRef var
-- :}
-- 10
-- @
module Test.Spec.Expr
  ( -- * Expressions
    Expr
  , constant
  , showConstant
  , statefun0
  , statefun1
  , statefun2
  , statefun3
  , variable
  , ($$)
  , constants
  , variables
  , assign
  , evaluate

  -- * Types
  , exprTypeArity
  , exprTypeRep
  , stateTypeRep
  , monadTypeRep
  , stateTyCon
  , monadTyCon
  ) where

import Data.Char (isAlphaNum)
import Data.Dynamic (dynApply, fromDynamic, toDyn)
import Data.List (intercalate, nub)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, TypeRep, TyCon, gcast, funResultTy, mkTyCon3, mkTyConApp, typeOf, typeRep)

import Test.Spec.Type

-------------------------------------------------------------------------------
-- Expressions

-- | An expression with effects in some monad @m@.
data Expr s m where
  -- It's important that these constructors aren't exposed, so the
  -- correctness of the 'TypeRep's can be ensured.
  Constant  :: Typeable a => String -> a -> TypeRep -> Expr s m
  Variable  :: String -> TypeRep -> Expr s m
  StateFun0 :: Typeable a => String -> (s -> m a) -> TypeRep -> Expr s m
  StateFun1 :: (Typeable a, Typeable b) => String -> (a -> s -> m b) -> TypeRep -> Expr s m
  StateFun2 :: (Typeable a, Typeable b, Typeable c) => String -> (a -> b -> s -> m c) -> TypeRep -> Expr s m
  StateFun3 :: (Typeable a, Typeable b, Typeable c, Typeable d) => String -> (a -> b -> c -> s -> m d) -> TypeRep -> Expr s m
  FunAp     :: Expr s m -> Expr s m -> TypeRep -> Expr s m

instance Show (Expr s m) where
  show = go True where
    go _ (Constant s _ _) = toPrefix s
    go _ (Variable s _) = toPrefix s
    go _ (StateFun0 s _ _) = toPrefix s
    go _ (StateFun1 s _ _) = toPrefix s
    go _ (StateFun2 s _ _) = toPrefix s
    go _ (StateFun3 s _ _) = toPrefix s
    go b ap =
      let inner = intercalate " " $ case unfoldAp ap of
            [(Constant s _ _), arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            [(Variable s _), arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            [(StateFun1 s _ _), arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            [(StateFun2 s _ _), arg1, arg2]
              | isSymbolic s -> [go False arg1, s, go False arg2]
            [(StateFun3 s _ _), arg1, arg2]
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
constant :: Typeable a => String -> a -> Expr s m
constant s a = Constant s a (typeOf a)

-- | A constant value from a type which can be shown.
showConstant :: (Show a, Typeable a) => a -> Expr s m
showConstant a = constant (show a) a

-- | A monadic function on the state.
statefun0 :: forall s m a. Typeable a => String -> (s -> m a) -> Expr s m
statefun0 s f = StateFun0 s f $ appFunTys stateTypeRep [monadTypeRep $ typeRep (Proxy :: Proxy a)]

-- | A monadic function on the state taking 1 other argument.
statefun1 :: forall s m a b. (Typeable a, Typeable b) => String -> (a -> s -> m b) -> Expr s m
statefun1 s f = StateFun1 s f $ appFunTys (typeRep (Proxy :: Proxy a)) [stateTypeRep, monadTypeRep $ typeRep (Proxy :: Proxy b)]

-- | A monadic function on the state taking 2 other arguments.
statefun2 :: forall s m a b c. (Typeable a, Typeable b, Typeable c) => String -> (a -> b -> s -> m c) -> Expr s m
statefun2 s f = StateFun2 s f $ appFunTys (typeRep (Proxy :: Proxy a)) [typeRep (Proxy :: Proxy b), stateTypeRep, monadTypeRep $ typeRep (Proxy :: Proxy c)]

-- | A monadic function on the state taking 3 other arguments.
statefun3 :: forall s m a b c d. (Typeable a, Typeable b, Typeable c, Typeable d) => String -> (a -> b -> c -> s -> m d) -> Expr s m
statefun3 s f = StateFun3 s f $ appFunTys (typeRep (Proxy :: Proxy a)) [typeRep (Proxy :: Proxy b), typeRep (Proxy :: Proxy c), stateTypeRep, monadTypeRep $ typeRep (Proxy :: Proxy d)]

-- | A variable.
variable :: Typeable a => String -> proxy a -> Expr s m
variable s = Variable s . typeRep

-- | Apply a function, if well-typed.
($$) :: Expr s m -> Expr s m -> Maybe (Expr s m)
f $$ e = FunAp f e <$> (exprTypeRep f `funResultTy` exprTypeRep e)

-- | Get all constants in an expression, without repetition.
constants :: Expr s m  -> [(String, TypeRep)]
constants = nub . go where
  go (Constant s _ ty) = [(s, ty)]
  go (FunAp f e _) = go f ++ go e
  go _ = []

-- | Get all variables in an expression, without repetition.
variables :: Expr s m -> [(String, TypeRep)]
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

-- | Evaluate an expression, if it has no free variables, all state
-- function applications are fully saturated, and it is the correct
-- type.
evaluate :: forall s m a. (Monad m, Typeable a) => s -> Expr s m -> Maybe (m a)
evaluate s = go where
  go :: forall b. Typeable b => Expr s m -> Maybe (m b)
  go (Constant _ a _) = gcast (pure a)
  go (StateFun0 _ f _) = gcast (f s)
  go (FunAp (StateFun1 _ f _) a _) = do
    a' <- go a
    gcast $ do { a'' <- a'; f a'' s}
  go (FunAp (FunAp (StateFun2 _ f _) a _) b _) = do
    a' <- go a
    b' <- go b
    gcast $ do { a'' <- a'; b'' <- b'; f a'' b'' s }
  go (FunAp (FunAp (FunAp (StateFun3 _ f _) a _) b _) c _) = do
    a' <- go a
    b' <- go b
    c' <- go c
    gcast $ do { a'' <- a'; b'' <- b'; c'' <- c'; f a'' b'' c'' s }
  go (FunAp f e _) = do
    f' <- dyngo f
    e' <- dyngo e
    fmap pure . fromDynamic =<< dynApply f' e'
  go _ = Nothing

  dyngo (Constant _ a _) = Just (toDyn a)
  dyngo (FunAp f e _) = do
    f' <- dyngo f
    e' <- dyngo e
    dynApply f' e'
  dyngo _ = Nothing


-------------------------------------------------------------------------------
-- Types

-- | Get the arity of an expression. Non-function types have an arity
-- of 0.
exprTypeArity :: Expr s m -> Int
exprTypeArity = typeArity . exprTypeRep

-- | Get the type of an expression.
exprTypeRep :: Expr s m -> TypeRep
exprTypeRep (Constant  _ _ ty) = ty
exprTypeRep (Variable  _   ty) = ty
exprTypeRep (FunAp     _ _ ty) = ty
exprTypeRep (StateFun0 _ _ ty) = ty
exprTypeRep (StateFun1 _ _ ty) = ty
exprTypeRep (StateFun2 _ _ ty) = ty
exprTypeRep (StateFun3 _ _ ty) = ty

-- | A 'TypeRep' for the state type. This is needed because, in
-- general, the state type may not be 'Typeable'.
stateTypeRep :: TypeRep
stateTypeRep = mkTyConApp stateTyCon []

-- | A 'TypeRep' for the monad type. This is needed because, in
-- general, the monad type may not be 'Typeable'.
monadTypeRep :: TypeRep -> TypeRep
monadTypeRep ty = mkTyConApp monadTyCon [ty]

-- | A 'TyCon' for the state type.
stateTyCon :: TyCon
stateTyCon = mkTyCon3 "" "" "state"

-- | A 'TyCon' for the monad type.
monadTyCon :: TyCon
monadTyCon = mkTyCon3 "" "" "monad"
