{-# LANGUAGE StrictData #-}

-- |
-- Module      : Test.Spec.Expr
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : StrictData
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
  , Schema
  , Term
  , toTerm
  , allTerms
    -- ** Construction
  , ($$)
  , bind
  , hole
  , let_
  , lit
  , commLit
  , showLit
  , stateVar
  -- ** Holes & Environment
  , envbind
  , environment
  , holes
  , rename
  -- ** Deconstruction
  , isApplication
  , isBind
  , isHole
  , isLet
  , isLit
  , isStateVar
  , unApplication
  , unBind
  , unLet
  , unLit
  -- ** Evaluation
  , evaluate
  , evaluateDyn
  -- ** Miscellaneous
  , Ignore(..)
  , exprSize
  , exprTypeArity
  , exprTypeRep
  , eq
  , pp
  ) where

import Data.Char (isAlphaNum)
import Data.Function (on)
import Data.List (groupBy, nub, sortOn)
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe, maybeToList)
import Data.Ord (Down(..))
import qualified Data.Typeable as T
import Data.Void (Void)

import Test.Spec.Type
import Test.Spec.Util

-------------------------------------------------------------------------------
-- Expressions

-- | An expression with effects in some monad @m@.
data Expr s m h
  -- It's important that these constructors aren't exposed, so the
  -- correctness of the 'TypeRep's can be ensured.
  = Lit Bool String (Dynamic s m)
  -- ^ @Lit True@ is a commutative lit, which affects function
  -- application.
  | Var (TypeRep s m) (Var h)
  -- ^ Holes, let-bound variables, and environment variables.
  | Let (TypeRep s m) Bool [Int] (Expr s m h) (Expr s m h)
  -- ^ @Let True@ is a monadic bind, which affects evaluation.
  | Ap  (TypeRep s m) (Expr s m h) (Expr s m h)
  -- ^ Function application.
  | StateVar
  -- ^ The state variable.
  deriving (Eq, Ord, Show)

-- | A hole or variable binding;
data Var h
  = Hole h
  -- ^ A typed hole.
  | Named String
  -- ^ A named variable from the environment.
  | Bound Int
  -- ^ A de Bruijn index.
  deriving (Eq, Ord, Show)

-- | A schema is an expression which may contain holes. One schema may
-- correspond to many terms.
type Schema s m = Expr s m ()

-- | A term is an expression with no holes. Many terms may correspond to one schema.
type Term s m = Expr s m Void

-- | Convert a 'Schema' to a 'Term' if there are no holes.
toTerm :: Schema s m -> Maybe (Term s m)
toTerm (Lit c s dyn) = Just (Lit c s dyn)
toTerm (Var ty v) = case v of
  Hole  _ -> Nothing
  Named s -> Just (Var ty (Named s))
  Bound i -> Just (Var ty (Bound i))
toTerm (Let ty m is b e) = Let ty m is <$> toTerm b <*> toTerm e
toTerm (Ap ty f e) = Ap ty <$> toTerm f <*> toTerm e
toTerm StateVar = Just StateVar

-- | From a schema that may have holes, generate a list of terms with
-- named variables substituted instead, ordered from most free (one
-- hole per variable) to most constrained (multiple holes per
-- variable).
--
-- This takes a function to assign a letter to each type, subsequent
-- variables of the same type have digits appended.
allTerms :: (T.TypeRep -> Char) -> Schema s m -> [Term s m]
allTerms nf = mapMaybe toTerm . sortOn (Down . length . environment) . go where
  go e0 = case hs e0 of
    [] -> [e0]
    (chosen:_) -> concatMap go
      [ e | ps <- partitions chosen
          , let (((_,tyc):_):_) = ps
          , let tyc' = rawTypeRep tyc
          , let vname i = if i == 0 then [nf tyc'] else nf tyc' : show (i::Int)
          , let naming = concat $ zipWith (\i vs -> [(v, vname i) | (v,_) <- vs]) [0..] ps
          , e <- maybeToList (envbind naming e0)
      ]

  -- holes grouped by type
  hs = groupBy ((==) `on` snd) . sortOn snd . holes

  -- all partitions of a list
  partitions (x:xs) =
    [[x]:p | p <- partitions xs] ++
    [(x:ys):yss | (ys:yss) <- partitions xs]
  partitions [] = [[]]


-------------------------------------------------------------------------------
-- Construction

-- | Apply a function, if well-typed.
--
-- @fmap exprSize (f $$ e) == Just (exprSize f + exprSize e)@
--
-- There are two special cases:
--
-- - See the comment of the 'Ignore' type for when it 'Ignore' is used
--   in a monadic parameter
--
-- - Applying the second argument to a commutative function produces
--   @Nothing@, even if well-typed, if it is @<@ the first argument.
($$) :: Ord h => Expr s m h -> Expr s m h -> Maybe (Expr s m h)
f $$ e = case funTys (exprTypeRep f) of
    Just (fArgTy, fResTy) ->
      -- check if the formal parameter is of type @m Ignore@ and the
      -- actual parameter is of type @m a@.
      if fArgTy == ignoreTypeRep && isJust (unmonad $ exprTypeRep e)
      then mkfun fResTy
      else mkfun =<< exprTypeRep f `funResultTy` exprTypeRep e
    Nothing -> Nothing
  where
    mkfun ty = case f of
      Ap _ (Lit True _ _) e0 | e < e0 -> Nothing
      _ -> Just (Ap ty f e)

-- | Bind a monadic value to a collection of holes, if well typed. The
-- numbering of unbound holes may be changed by this function.
--
-- @fmap exprSize (bind is b e) == Just (1 + exprSize b + exprSize e)@
bind :: [Int] -- ^ Holes.
     -> Expr s m h -- ^ Expression to bind
     -> Expr s m h -- ^ Expression to bind variable in
     -> Maybe (Expr s m h)
bind is binder body = do
  _ <- unmonad (exprTypeRep body)
  innerTy <- unmonad (exprTypeRep binder)
  Let (exprTypeRep body) True is binder <$> letHelper is innerTy body

-- | A typed hole.
--
-- @exprSize (hole proxy) == 1@
hole :: HasTypeRep s m a => proxy a -> Expr s m ()
hole p = Var (typeRep p) (Hole ())

-- | Bind a value to a collection of holes, if well typed. The
-- numbering of unbound holes may be changed by this function.
--
-- @fmap exprSize (let_ is b e) == Just (1 + exprSize b + exprSize e)@
let_ :: [Int] -- ^ Holes.
     -> Expr s m h -- ^ Expression to bind
     -> Expr s m h -- ^ Expression to bind variable in
     -> Maybe (Expr s m h)
let_ is binder body =
  Let (exprTypeRep body) False is binder <$> letHelper is (exprTypeRep binder) body

-- | A literal value.
--
-- @exprSize (lit "foo" foo) == 1@
lit :: HasTypeRep s m a => String -> a -> Expr s m h
lit s a = Lit False s (toDyn a)

-- | A commutative binary function. Used to avoid redundancies in term
-- generation.
--
-- @commLit "foo" foo == 1@
commLit :: HasTypeRep s m a => String -> a -> Expr s m h
commLit s a = Lit True s (toDyn a)

-- | A literal value from a type which can be shown.
--
-- @exprSize (showLit foo) == 1@
showLit :: (Show a, HasTypeRep s m a) => a -> Expr s m h
showLit a = lit (show a) a

-- | The state variable
--
-- @exprSize stateVar == 1@
stateVar :: Expr s m h
stateVar = StateVar


-------------------------------------------------------------------------------
-- Environment & Holes

-- | Bind holes to environment variables, if all have the same
-- type. The numbering of unbound holes may be changed by this
-- function.
envbind :: [(Int, String)] -> Expr s m h -> Maybe (Expr s m h)
envbind is e0 = (\(e,_,_) -> e) <$> go [] 0 e0 where
  go env i n@(Var ty (Named s)) = case lookup s env of
    Just sty
      | ty == sty -> Just (n, env, i)
      | otherwise -> Nothing
    Nothing -> Just (n, env, i)
  go env i (Var ty (Hole h)) = case lookup i is of
    Just s -> case lookup s env of
      Just sty
        | ty == sty -> Just (Var ty (Named s), env, i + 1)
        | otherwise -> Nothing
      Nothing -> Just (Var ty (Named s), (s,ty):env, i + 1)
    Nothing -> Just (Var ty (Hole h), env, i + 1)
  go env i (Let ty m js b e) = do
    (b', env',  i')  <- go env  i  b
    (e', env'', i'') <- go env' i' e
    Just (Let ty m js b' e', env'', i'')
  go env i (Ap ty f e) = do
    (f', env',  i')  <- go env  i  f
    (e', env'', i'') <- go env' i' e
    Just (Ap ty f' e', env'', i'')
  go env i e = Just (e, env, i)

-- | Get all the environment variables in an expression.
environment :: Expr s m h -> [(String, TypeRep s m)]
environment = nub . go where
  go (Var ty (Named s)) = [(s, ty)]
  go (Let _ _ _ b e) = go b ++ go e
  go (Ap _ f e) = go f ++ go e
  go _ = []

-- | Rename variables in an expression, assuming a consistent
-- renaming.
rename :: [(String, String)] -> Expr s m h -> Expr s m h
rename rs = go where
  go (Var ty (Named s)) = Var ty (Named . fromMaybe s $ lookup s rs)
  go (Var ty v) = Var ty v
  go (Let ty m js b e) = Let ty m js (go b) (go e)
  go (Ap ty f e) = Ap ty (go f) (go e)
  go e = e

-- | Get all holes in an expression, tagged with their position.
holes :: Expr s m h -> [(Int, TypeRep s m)]
holes = fst . go 0 where
  go i (Var ty (Hole _)) = ([(i, ty)], i + 1)
  go i (Let _ _ _ b e) =
    let (bhs, i')  = go i  b
        (ehs, i'') = go i' e
    in (bhs ++ ehs, i'')
  go i (Ap _ f e) =
    let (fhs, i')  = go i  f
        (ehs, i'') = go i' e
    in (fhs ++ ehs, i'')
  go i _ = ([], i)


-------------------------------------------------------------------------------
-- Deconstruction

-- | Check if an expression is a function application.
isApplication :: Expr s m h -> Bool
isApplication = isJust . unApplication

-- | Check if an expression is a monadic bind.
isBind :: Expr s m h -> Bool
isBind = isJust . unBind

-- | Check if an expression is a typed hole.
isHole :: Expr s m h -> Bool
isHole (Var _ (Hole _)) = True
isHole _ = False

-- | Check if an expression is a let binding.
isLet :: Expr s m h -> Bool
isLet = isJust . unLet

-- | Check if an expression is a literal.
isLit :: Expr s m h -> Bool
isLit = isJust . unLit

-- | Check if an expression is the state variable.
isStateVar :: Expr s m h -> Bool
isStateVar StateVar = True
isStateVar _ = False

-- | Deconstruct a function application.
unApplication :: Expr s m h -> Maybe (Expr s m h, Expr s m h)
unApplication (Ap _ f e) = Just (f, e)
unApplication _ = Nothing

-- | Deconstruct a monadic bind.
unBind :: Expr s m h -> Maybe ([Int], Expr s m h, Expr s m h)
unBind (Let _ True is b e) = Just (is, b, e)
unBind _ = Nothing

-- | Deconstruct a let binding.
unLet :: Expr s m h -> Maybe ([Int], Expr s m h, Expr s m h)
unLet (Let _ False is b e) = Just (is, b, e)
unLet _ = Nothing

-- | Deconstruct a literal.
unLit :: Expr s m h -> Maybe (String, Dynamic s m)
unLit (Lit _ s dyn) = Just (s, dyn)
unLit _ = Nothing


-------------------------------------------------------------------------------
-- Evaluation

-- | Evaluate an expression, if the environment is complete and it is
-- the correct type.
--
-- If the outer 'Maybe' is @Nothing@, the environment is
-- incomplete. If the inner 'Maybe' is @Nothing@, the type is
-- incorrect.
evaluate :: (Monad m, HasTypeRep s m a) => Term s m -> [(String, Dynamic s m)] -> Maybe (s -> Maybe a)
evaluate e0 globals = (fromDyn .) <$> evaluateDyn e0 globals

-- | Evaluate an expression, if the environment is complete.
evaluateDyn :: Monad m => Term s m -> [(String, Dynamic s m)] -> Maybe (s -> Dynamic s m)
evaluateDyn e0 globals
    | all check (environment e0) = Just (go [] e0)
    | otherwise = Nothing
  where
    -- The various errors in this function shouldn't happen, as
    -- @evaluateDyn@ checks there are no free variables, and the
    -- various smart constructors check the types match.
    go _ (Lit _ _ dyn) _ = dyn
    go locals (Var _ var) _ =
      unmaybe ("unexpected free variable " ++ show var ++ " in expression") $ env locals var
    go locals (Let ty True _ b e) s =
      let mx = unmaybe ("can't bind non-monadic expression " ++ show b ++ " in body " ++ show e) $ unwrapMonadicDyn (go locals b s)
      in unsafeWrapMonadicDyn ty $ mx >>= \x -> unmaybe ("non-monadic result of bind: " ++ show e) (unwrapMonadicDyn (go (x:locals) e s))
    go locals (Let _ False _ b e) s =
      let x = go locals b s
      in go (x:locals) e s
    go locals (Ap _ f e) s =
      let f' = go locals f s
          e' = go locals e s
      in unmaybe ("can't apply function " ++ show f ++ " to argument " ++ show e) $ f' `dynApp` (if ignoreArg f' then ignore e' else e')
    go _ StateVar s = toDyn s

    env locals (Bound i) = Just (locals !! i)
    env _ (Named s) = lookup s globals
    env _ (Hole _) = Nothing -- unreachable

    ignoreArg fdyn = case funTys (dynTypeRep fdyn) of
      Just (fArgTy, _) -> fArgTy == ignoreTypeRep
      Nothing -> error ("can't handle non-function type " ++ show fdyn)

    ignore dyn = case unwrapMonadicDyn dyn of
      Just ma -> unsafeToDyn (rawTypeRep ignoreTypeRep) (const Ignore <$> ma)
      Nothing -> error ("can't ignore non-monadic value " ++ show dyn)

    check (s, ty) = case lookup s globals of
      Just dyn -> dynTypeRep dyn == ty
      Nothing -> False


-------------------------------------------------------------------------------
-- Misc

-- | A special type for enabling basic polymorphism.
--
-- A function parameter of type @m Ignore@ unifies with values of any
-- type @m a@, where @fmap (const Ignore)@ is applied to the parameter
-- automatically. This avoids the need to clutter expressions with
-- calls to 'void', or some other such function.
data Ignore = Ignore
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | Get the arity of an expression. Non-function types have an arity
-- of 0.
exprTypeArity :: Expr s m h -> Int
exprTypeArity = typeArity . exprTypeRep

-- | Get the type of an expression.
exprTypeRep :: Expr s m h -> TypeRep s m
exprTypeRep (Lit _ _ dyn) = dynTypeRep dyn
exprTypeRep (Var ty _) = ty
exprTypeRep (Let ty _ _ _ _) = ty
exprTypeRep (Ap ty _ _) = ty
exprTypeRep StateVar = stateTypeRep

-- | Get the size of an expression.
exprSize :: Expr s m h -> Int
exprSize (Let _ _ _ b e) = 1 + exprSize b + exprSize e
exprSize (Ap _ f e) = exprSize f + exprSize e
exprSize _ = 1

-- | Check if two expressions are equal, disregarding monad, state,
-- and hole types.
eq :: Expr s1 m1 h1 -> Expr s2 m2 h2 -> Bool
eq (Lit _ _ dyn1) (Lit _ _ dyn2) = rawTypeRep (dynTypeRep dyn1) == rawTypeRep (dynTypeRep dyn2)
eq (Var ty1 v1) (Var ty2 v2) = rawTypeRep ty1 == rawTypeRep ty2 && case (v1, v2) of
  (Hole _, Hole _) -> True
  (Bound i1, Bound i2) -> i1 == i2
  (Named s1, Named s2) -> s1 == s2
  _ -> False
eq (Let ty1 m1 is1 b1 e1) (Let ty2 m2 is2 b2 e2) =
  rawTypeRep ty1 == rawTypeRep ty2 &&
  m1  == m2  &&
  is1 == is2 &&
  b1 `eq` b2 &&
  e1 `eq` e2
eq (Ap ty1 f1 e1) (Ap ty2 f2 e2) =
  rawTypeRep ty1 == rawTypeRep ty2 &&
  f1 `eq` f2 &&
  e1 `eq` e2
eq StateVar StateVar = True
eq _ _ = False

-- | Pretty-print an expression.
pp :: (T.TypeRep -> Char) -> Expr s m h -> String
pp nf e0 = go [] True e0 where
  go _ _ (Lit _ s _) = toPrefix s
  go env top (Var ty v) = case v of
    Hole _ -> wrap top ("_ :: " ++ show ty)
    Bound i -> env !! i
    Named s -> s
  go _ _ StateVar = ":state:"
  go env top e = wrap top . unwords $ case e of
    Let _ True is b x ->
      let v = fresh env (fromJust . unmonad $ exprTypeRep b)
          sb = go env top b
          se = go (v:env) top x
      in if null is
         then [sb, ">>", se]
         else [sb, ">>=", '\\': v, "->", se]
    Let _ False _ b x ->
      let v = fresh env (exprTypeRep b)
          sb = go env top b
          se = go (v:env) top x
      in ["let", v, "=", sb, "in", se]
    Ap _ _ _ -> case unfoldAp e of
      [Lit _ s _, arg1, arg2]
        | isSymbolic s -> [go env False arg1, s, go env False arg2]
      [Var _ (Named s), arg1, arg2]
        | isSymbolic s -> [go env False arg1, s, go env False arg2]
      [Var _ (Bound i), arg1, arg2]
        | isSymbolic (env!!i) -> [go env False arg1, env!!i, go env False arg2]
      unfolded -> map (go env False) unfolded
    _ -> [] -- shouldn't be reached

  unfoldAp (Ap _ f e) = unfoldAp f ++ [e]
  unfoldAp e = [e]

  wrap True  s = s
  wrap False s = "(" ++ s ++ ")"

  toPrefix s
    | not (isSymbolic s) = s
    | otherwise = "(" ++ s ++ ")"

  isSymbolic = not . all (\c -> isAlphaNum c || c == '_' || c == '\'')

  fresh env = head . dropWhile (\v -> v `elem` env || any ((==v) . fst) (environment e0)) . names
  names ty =
    let ty' = rawTypeRep ty
    in [nf ty'] : [ nf ty' : show (i::Int) | i <- [1..]]

-------------------------------------------------------------------------------
-- Utils

-- | Helper for 'bind' and 'let_': bind holes to the top of the expression.
letHelper :: [Int] -> TypeRep s m -> Expr s m h -> Maybe (Expr s m h)
letHelper is boundTy e0 = fst <$> go 0 0 e0 where
  go n i (Var ty (Hole h))
    | i `elem` is = if boundTy == ty then Just (Var ty (Bound n), i + 1) else Nothing
    | otherwise   = Just (Var ty (Hole h), i + 1)
  go n i (Let ty m js b e) = do
    (b', i')  <- go n     i  b
    (e', i'') <- go (n+1) i' e
    Just (Let ty m js b' e', i'')
  go n i (Ap ty f e) = do
    (f', i')  <- go n i  f
    (e', i'') <- go n i' e
    Just (Ap ty f' e', i'')
  go _ i e = Just (e, i)

-- | The typerep for @m Ignore@.
ignoreTypeRep :: TypeRep s m
ignoreTypeRep = monadTypeRep (T.typeOf Ignore)
