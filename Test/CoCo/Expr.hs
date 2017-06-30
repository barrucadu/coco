{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}

-- |
-- Module      : Test.CoCo.Expr
-- Copyright   : (c) 2017 Michael Walker
-- License     : MIT
-- Maintainer  : Michael Walker <mike@barrucadu.co.uk>
-- Stability   : experimental
-- Portability : ScopedTypeVariables, StrictData
--
-- Constructing and evaluating dynamically-typed monadic expressions.
module Test.CoCo.Expr
  ( -- * Expressions
    Expr
  , Schema
  , Term
  , toTerm
  , allTerms
  , isInstanceOf
  , findInstance
    -- ** Construction
  , ($$)
  , bind
  , hole
  , holeOf
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
  , subterms
  -- ** Evaluation
  , evaluate
  , evaluateDyn
  , evaluateDynPure
  -- ** Miscellaneous
  , exprSize
  , exprTypeArity
  , exprType
  , instantiateTys
  , eq
  , pp
  ) where

import           Control.Monad   (guard)
import           Data.Char       (isAlphaNum)
import           Data.Function   (on)
import           Data.List       (groupBy, nub, sortOn)
import           Data.Maybe      (fromJust, fromMaybe, isJust, mapMaybe,
                                  maybeToList)
import           Data.Ord        (Down(..))
import           Data.Proxy      (Proxy(..))
import           Data.Typeable   (Typeable)
import           Data.Void       (Void)

import           Test.CoCo.Monad (Concurrency)
import           Test.CoCo.Type
import           Test.CoCo.Util

-------------------------------------------------------------------------------
-- Expressions

-- | An expression with effects in some monad @m@.
data Expr s h
  -- It's important that these constructors aren't exposed, so the
  -- correctness of the 'Type's can be ensured.
  = Lit Bool String Dynamic
  -- ^ @Lit True@ is a commutative lit, which affects function
  -- application.
  | Var Type (Var h)
  -- ^ Holes, let-bound variables, and environment variables.
  | Let Type Bool [Int] (Expr s h) (Expr s h)
  -- ^ @Let True@ is a monadic bind, which affects evaluation.
  | Ap  Type (Expr s h) (Expr s h)
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
type Schema s = Expr s ()

-- | A term is an expression with no holes. Many terms may correspond to one schema.
type Term s = Expr s Void

-- | Convert a 'Schema' to a 'Term' if there are no holes.
toTerm :: Schema s -> Maybe (Term s)
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
allTerms :: (Type -> Char) -> Schema s -> [Term s]
allTerms nf = mapMaybe toTerm . sortOn (Down . length . environment) . go where
  go e0 = case hs e0 of
    [] -> [e0]
    (chosen:_) -> concatMap go
      [ e | ps <- partitions chosen
          , let (((_,tyc):_):_) = ps
          , let vname i = if i == 0 then [nf tyc] else nf tyc : show (i::Int)
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

-- | Check if one expression is an instance of another (this is a
-- partial ordering).
--
-- An expression is an instance of another if (a) they have the same
-- shape, and (b) the variables of the \"lesser\" are subsumed by the
-- \"greater\". For some intuition, consider an extreme case:
--
-- @
-- f a b == g c d
-- f a a == g c c
-- @
--
-- Clearly if the first property is true, then the second will as
-- well. The first is more general in that it imposes fewer
-- constraints on the values of the holes. The latter is more specific
-- as it imposes two constraints.
--
-- This is intended to be used infix, so the argument order is
-- @specific `isInstanceOf` general@
isInstanceOf :: Expr s1 h1 -> Expr s2 h2 -> Bool
isInstanceOf eS eG = ok && checkEnv (sortGroupTagged envG) (sortGroupTagged envS) where
  (ok, envG, envS, _) = checkShape (0::Int) eG eS

  checkShape i (Lit b1 s1 dyn1) (Lit b2 s2 dyn2) = (b1 == b2 && s1 == s2 && dyn1 `deq` dyn2, [], [], i)
  checkShape i (Var ty1 (Hole  _))  (Var ty2 (Hole  _))  = (ty1 == ty2, [], [], i)
  checkShape i (Var ty1 (Named s1)) (Var ty2 (Named s2)) = (ty1 == ty2, [(s1, i)], [(s2, i)], i+1)
  checkShape i (Var ty1 (Bound i1)) (Var ty2 (Bound i2)) = (ty1 == ty2 && i1 == i2, [], [], i)
  checkShape i (Let ty1 m1 is1 b1 e1) (Let ty2 m2 is2 b2 e2) =
    let (bok, benv1, benv2, i')  = checkShape i  b1 b2
        (eok, eenv1, eenv2, i'') = checkShape i' e1 e2
    in (ty1 == ty2 && m1 == m2 && is1 == is2 && bok && eok, nub (benv1++eenv1), nub (benv2++eenv2), i'')
  checkShape i (Ap ty1 f1 e1) (Ap ty2 f2 e2) =
    let (fok, fenv1, fenv2, i')  = checkShape i  f1 f2
        (eok, eenv1, eenv2, i'') = checkShape i' e1 e2
    in (ty1 == ty2 && fok && eok, nub (fenv1++eenv1), nub (fenv2++eenv2), i'')
  checkShape i StateVar StateVar = (True, [], [], i)
  checkShape i _ _ = (False, [], [], i)

  checkEnv (as:ass) bss =
    any (\bs -> all (`elem` bs) as) bss && checkEnv ass bss
  checkEnv [] _ = True

  deq dyn1 dyn2 = dynType dyn1 == dynType dyn2

  -- group a list of tuples by first element (the tag) and then discard it.
  sortGroupTagged = map (map snd) . groupBy ((==) `on` fst) . sortOn fst

-- | If one expression is an instance of another, find the mapping
-- from variable names in the more specific instance to lists of
-- variables in the more general instance.
findInstance
  :: Expr s1 h1 -- ^ The more generic term.
  -> Expr s2 h2 -- ^ The more specific term.
  -> Maybe [(String, [String])]
findInstance eG eS
    | eS `isInstanceOf` eG = Just nameMap
    | otherwise = Nothing
  where
    env = map fst . environment'
    nameMap =
      map (\((s,g):sgs) -> (s, nub (g:map snd sgs))) .
      groupBy ((==) `on` fst) .
      sortOn fst $
      zip (env eS) (env eG)


-------------------------------------------------------------------------------
-- Construction

-- | Apply a function, if well-typed.
--
-- @fmap exprSize (f $$ e) == Just (exprSize f + exprSize e)@
--
-- Applying the second argument to a commutative function produces
-- @Nothing@, even if well-typed, if it is @<@ the first argument.
($$) :: (Typeable s, Ord h) => Expr s h -> Expr s h -> Maybe (Expr s h)
f0 $$ e0 = do
  guard $ case f0 of Ap _ (Lit True _ _) e -> e0 >= e; _ -> True
  tys <- exprType f0 `polyApplyFunTy'` exprType e0
  runUnify $ do
    (argTy, resTy) <- tys
    f <- instantiateTys f0
    pure (Ap resTy f (setType argTy e0))

-- | Bind a monadic value to a collection of holes, if well typed. The
-- numbering of unbound holes may be changed by this function.
--
-- @fmap exprSize (bind is b e) == Just (1 + exprSize b + exprSize e)@
bind :: Typeable s
  => [Int] -- ^ Holes.
  -> Expr s h -- ^ Expression to bind
  -> Expr s h -- ^ Expression to bind variable in
  -> Maybe (Expr s h)
bind is binder body = do
  _ <- unmonad body
  inner <- unmonad binder
  Let (exprType body) True is binder <$> letHelper is inner body

-- | A typed hole.
--
-- @exprSize (hole proxy) == 1@
hole :: Typeable a => proxy a -> Expr s ()
hole p = Var (typeRep p) (Hole ())

-- | A typed hole (from a 'TypeRep'). If given the state type, this is
-- equivalent to 'stateVar'.
--
-- @exprSize (holeOf ty) == 1@
holeOf :: forall s. Typeable s => Type -> Expr s ()
holeOf ty
  | ty `unifies` (typeRep (Proxy :: Proxy s)) = stateVar
  | otherwise = Var ty (Hole ())

-- | Bind a value to a collection of holes, if well typed. The
-- numbering of unbound holes may be changed by this function.
--
-- @fmap exprSize (let_ is b e) == Just (1 + exprSize b + exprSize e)@
let_ :: Typeable s
  => [Int] -- ^ Holes.
  -> Expr s h -- ^ Expression to bind
  -> Expr s h -- ^ Expression to bind variable in
  -> Maybe (Expr s h)
let_ is binder body =
  Let (exprType body) False is binder <$> letHelper is (exprType binder) body

-- | A literal value.
--
-- @exprSize (lit "foo" foo) == 1@
lit :: Typeable a => String -> a -> Expr s h
lit s a = Lit False s (toDyn a)

-- | A commutative binary function. Used to avoid redundancies in term
-- generation.
--
-- @commLit "foo" foo == 1@
commLit :: Typeable a => String -> a -> Expr s h
commLit s a = Lit True s (toDyn a)

-- | A literal value from a type which can be shown.
--
-- @exprSize (showLit foo) == 1@
showLit :: (Show a, Typeable a) => a -> Expr s h
showLit a = lit (show a) a

-- | The state variable
--
-- @exprSize stateVar == 1@
stateVar :: Expr s h
stateVar = StateVar


-------------------------------------------------------------------------------
-- Environment & Holes

-- | Bind holes to environment variables, if all have the same
-- type. The numbering of unbound holes may be changed by this
-- function.
envbind :: [(Int, String)] -> Expr s h -> Maybe (Expr s h)
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
environment :: Expr s h -> [(String, Type)]
environment = nub . environment'

-- | Get all the environment variables in an expression, with
-- repetition, in the order in which they appear in the expression.
environment' :: Expr s h -> [(String, Type)]
environment' = go where
  go (Var ty (Named s)) = [(s, ty)]
  go (Let _ _ _ b e) = go b ++ go e
  go (Ap _ f e) = go f ++ go e
  go _ = []

-- | Rename variables in an expression, assuming a consistent
-- renaming.
rename :: [(String, String)] -> Expr s h -> Expr s h
rename rs = go where
  go (Var ty (Named s)) = Var ty (Named . fromMaybe s $ lookup s rs)
  go (Var ty v) = Var ty v
  go (Let ty m js b e) = Let ty m js (go b) (go e)
  go (Ap ty f e) = Ap ty (go f) (go e)
  go e = e

-- | Get all holes in an expression, tagged with their position.
holes :: Expr s h -> [(Int, Type)]
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
isApplication :: Expr s h -> Bool
isApplication = isJust . unApplication

-- | Check if an expression is a monadic bind.
isBind :: Expr s h -> Bool
isBind = isJust . unBind

-- | Check if an expression is a typed hole.
isHole :: Expr s h -> Bool
isHole (Var _ (Hole _)) = True
isHole _ = False

-- | Check if an expression is a let binding.
isLet :: Expr s h -> Bool
isLet = isJust . unLet

-- | Check if an expression is a literal.
isLit :: Expr s h -> Bool
isLit = isJust . unLit

-- | Check if an expression is the state variable.
isStateVar :: Expr s h -> Bool
isStateVar StateVar = True
isStateVar _ = False

-- | Deconstruct a function application.
unApplication :: Expr s h -> Maybe (Expr s h, Expr s h)
unApplication (Ap _ f e) = Just (f, e)
unApplication _ = Nothing

-- | Deconstruct a monadic bind.
unBind :: Expr s h -> Maybe ([Int], Expr s h, Expr s h)
unBind (Let _ True is b e) = Just (is, b, e)
unBind _ = Nothing

-- | Deconstruct a let binding.
unLet :: Expr s h -> Maybe ([Int], Expr s h, Expr s h)
unLet (Let _ False is b e) = Just (is, b, e)
unLet _ = Nothing

-- | Deconstruct a literal.
unLit :: Expr s h -> Maybe (String, Dynamic)
unLit (Lit _ s dyn) = Just (s, dyn)
unLit _ = Nothing

-- | All subterms of an expression, including the expression itself.
subterms :: Expr s h -> [Expr s h]
subterms e@(Let _ _ _ e1 e2) = e : subterms e1 ++ subterms e2
subterms e@(Ap  _     e1 e2) = e : subterms e1 ++ subterms e2
subterms e = [e]

-------------------------------------------------------------------------------
-- Evaluation

-- | Evaluate an expression, if the environment is complete and it is
-- the correct type.
--
-- If the outer 'Maybe' is @Nothing@, the environment is
-- incomplete. If the inner 'Maybe' is @Nothing@, the type is
-- incorrect.
evaluate :: (Typeable s, Typeable a) => Term s -> [(String, Dynamic)] -> Maybe (s -> Maybe a)
evaluate e0 globals = (fromDyn .) <$> evaluateDyn e0 globals

-- | Evaluate an expression, if the environment is complete.
evaluateDyn :: forall s. Typeable s => Term s -> [(String, Dynamic)] -> Maybe (s -> Dynamic)
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
      let mx = unmaybe ("can't bind non-monadic expression " ++ show b ++ " in body " ++ show e) $ unFunctor (go locals b s)
      in unsafeWrapFunctorDyn ty $ mx >>= \x -> unmaybe ("non-monadic result of bind: " ++ show e) (unFunctor (go (x:locals) e s))
    go locals (Let _ False _ b e) s =
      let x = go locals b s
      in go (x:locals) e s
    go locals (Ap _ f e) s =
      let f' = go locals f s
          e' = go locals e s
      in unmaybe ("can't apply function " ++ show f ++ " to argument " ++ show e) $ f' `dynApp` e'
    go _ StateVar s = toDyn s

    env locals (Bound i) = Just (locals !! i)
    env _ (Named s) = lookup s globals
    env _ (Hole _) = Nothing -- unreachable

    check (s, ty) = case lookup s globals of
      Just dyn -> dynType dyn == ty
      Nothing -> False

    unFunctor :: Dynamic -> Maybe (Concurrency Dynamic)
    unFunctor = unwrapFunctorDyn

-- | Evaluate a pure expression, if the environment is complete.
-- Evaluation fails if the seed or a monadic bind is involved
-- anywhere.
evaluateDynPure :: Term s -> [(String, Dynamic)] -> Maybe Dynamic
evaluateDynPure e0 globals = go [] e0 where
  go _ (Lit _ _ dyn) = Just dyn
  go locals (Var _ var) = env locals var
  go locals (Let _ False _ b e) = do
    x <- go locals b
    go (x:locals) e
  go locals (Ap _ f e) = do
    f' <- go locals f
    e' <- go locals e
    f' `dynApp` e'
  go _ _ = Nothing

  env locals (Bound i) = Just (locals !! i)
  env _ (Named s) = lookup s globals
  env _ (Hole _) = Nothing


-------------------------------------------------------------------------------
-- Misc

-- | Get the arity of an expression. Non-function types have an arity
-- of 0.
exprTypeArity :: Typeable s => Expr s h -> Int
exprTypeArity = typeArity . exprType

-- | Get the type of an expression.
exprType :: forall s h. Typeable s => Expr s h -> Type
exprType (Lit _ _ dyn) = dynType dyn
exprType (Var ty _) = ty
exprType (Let ty _ _ _ _) = ty
exprType (Ap ty _ _) = ty
exprType StateVar = typeRep (Proxy :: Proxy s)

-- | Get the size of an expression.
exprSize :: Expr s h -> Int
exprSize (Let _ _ _ b e) = 1 + exprSize b + exprSize e
exprSize (Ap _ f e) = exprSize f + exprSize e
exprSize _ = 1

-- | Instantiate polymorphic type variables according to the current
-- environment.
instantiateTys :: Expr s h -> UnifyM (Expr s h)
instantiateTys (Lit b s d) =
  Lit b s <$> dynApplyBindings d
instantiateTys (Var ty v) =
  Var <$> applyBindings ty <*> pure v
instantiateTys (Let ty m is b e) =
  Let <$> applyBindings ty <*> pure m <*> pure is <*> instantiateTys b <*> instantiateTys e
instantiateTys (Ap ty f e) =
  Ap <$> applyBindings ty <*> instantiateTys f <*> instantiateTys e
instantiateTys e = pure e

-- | Check if two expressions are equal, disregarding state and hole
-- types.
eq :: Expr s1 h1 -> Expr s2 h2 -> Bool
eq (Lit _ _ dyn1) (Lit _ _ dyn2) = dynType dyn1 == dynType dyn2
eq (Var ty1 v1) (Var ty2 v2) = ty1 == ty2 && case (v1, v2) of
  (Hole _, Hole _) -> True
  (Bound i1, Bound i2) -> i1 == i2
  (Named s1, Named s2) -> s1 == s2
  _ -> False
eq (Let ty1 m1 is1 b1 e1) (Let ty2 m2 is2 b2 e2) =
  ty1 == ty2 &&
  m1  == m2  &&
  is1 == is2 &&
  b1 `eq` b2 &&
  e1 `eq` e2
eq (Ap ty1 f1 e1) (Ap ty2 f2 e2) =
  ty1 == ty2 &&
  f1 `eq` f2 &&
  e1 `eq` e2
eq StateVar StateVar = True
eq _ _ = False

-- | Pretty-print an expression.
pp :: Typeable s
  => (Type -> Char)
  -- ^ Variable-naming function.
  -> Bool
  -- ^ If True use the name \"h0\" for the state otherwise use \"@\".
  -> Expr s h
  -- ^ Expression to pretty-print.
  -> String
pp nf sn e0 = go [] True e0 where
  go _ _ (Lit _ s _) = toPrefix s
  go env top (Var ty v) = case v of
    Hole _ -> wrap top ("_ :: " ++ show ty)
    Bound i -> env !! i
    Named s -> s
  go _ _ StateVar = if sn then "h0" else "@"
  go env top e = wrap top . unwords $ case e of
    Let _ True is b x ->
      let v = fresh env . fromJust $ unmonad b
          sb = go env top b
          se = go (v:env) top x
      in if null is
         then [sb, ">>", se]
         else [sb, ">>=", '\\': v, "->", se]
    Let _ False _ b x ->
      let v = fresh env (exprType b)
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
  names ty = [nf ty] : [ nf ty : show (i::Int) | i <- [1..]]


-------------------------------------------------------------------------------
-- Utils

-- | Set the type of an expression.
setType :: Type -> Expr s h -> Expr s h
setType ty (Lit b s d) = Lit b s (unsafeSetType ty d)
setType ty (Var _ v) = Var ty v
setType ty (Let _ m is b e) = Let ty m is b e
setType ty (Ap _ f e) = Ap ty f e
setType _ StateVar = StateVar

-- | Helper for 'bind' and 'let_': bind holes to the top of the expression.
letHelper :: [Int] -> Type -> Expr s h -> Maybe (Expr s h)
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

-- | Peel off the @Concurrency@ tycon
unmonad :: forall s h. Typeable s => Expr s h -> Maybe Type
unmonad = innerTy (Proxy :: Proxy Concurrency) . exprType
