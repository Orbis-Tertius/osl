{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}


module Semicircuit.Sigma11
  ( prependBounds
  , prependQuantifiers
  , prependArguments
  ) where


import Semicircuit.Types.Sigma11 (ExistentialQuantifier (Some, SomeP), InputBound (..), Quantifier (Universal, Existential), Formula (ForAll, ForSome, Equal, LessOrEqual, Predicate, Not, And, Or, Implies, Iff), Term (App, AppInverse, Add, Mul, IndLess, Const), Name, var, Bound (TermBound, FieldMaxBound), OutputBound (..))


prependBounds
  :: [InputBound]
  -> ExistentialQuantifier
  -> ExistentialQuantifier
prependBounds bs' (Some x n bs b) =
  Some x n (bs' <> bs) b
prependBounds _ (SomeP _ _ _ _) =
  error "there is a compiler bug; applied prependBounds to SomeP"


prependQuantifiers :: [Quantifier] -> Formula -> Formula
prependQuantifiers qs f =
  foldl (flip prependQuantifier) f qs


prependQuantifier :: Quantifier -> Formula -> Formula
prependQuantifier (Universal x b) f =
  ForAll x b f
prependQuantifier (Existential q) f =
  ForSome q f


-- Prepends the given arguments to all applications
-- of the given name. This substitution does not need
-- to account for name shadowing, since all gensyms
-- are globally unique.
prependArguments :: Name -> [Name] -> Formula -> Formula
prependArguments f xs =
  \case
    Equal a b -> Equal (term a) (term b)
    LessOrEqual a b -> LessOrEqual (term a) (term b)
    Predicate p xs' -> Predicate p (term <$> xs')
    Not p -> Not (rec p)
    And p q -> And (rec p) (rec q)
    Or p q -> Or (rec p) (rec q)
    Implies p q -> Implies (rec p) (rec q)
    Iff p q -> Iff (rec p) (rec q)
    ForAll x b p -> ForAll x (mapBound term b) (rec p)
    ForSome q p ->
      ForSome (mapExistentialQuantifierBounds term q) (rec p)
  where
    rec = prependArguments f xs

    term =
      \case
        App g xs' ->
          if g == f
          then App g ((var <$> xs) <> xs')
          else App g xs'
        AppInverse g x ->
          if g == f
          then error $ "prependArguments of AppInverse f: "
            <> "this is a compiler bug"
          else AppInverse g x
        Add x y ->
          Add (term x) (term y)
        Mul x y ->
          Mul (term x) (term y)
        IndLess x y ->
          IndLess (term x) (term y)
        Const x -> Const x


mapBound :: (Term -> Term) -> Bound -> Bound
mapBound f =
  \case
    TermBound x -> TermBound (f x)
    FieldMaxBound -> FieldMaxBound


mapInputBound :: (Term -> Term) -> InputBound -> InputBound
mapInputBound f (InputBound x b) =
  InputBound x (mapBound f b)


mapOutputBound :: (Term -> Term) -> OutputBound -> OutputBound
mapOutputBound f (OutputBound b) =
  OutputBound (mapBound f b)


mapExistentialQuantifierBounds
  :: (Term -> Term)
  -> (ExistentialQuantifier -> ExistentialQuantifier)
mapExistentialQuantifierBounds f =
  \case
    Some x n bs b ->
      Some x n (mapInputBound f <$> bs) (mapOutputBound f b)
    SomeP x n b0 b1 ->
      SomeP x n (mapInputBound f b0) (mapOutputBound f b1)
