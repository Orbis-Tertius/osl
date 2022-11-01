{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module Semicircuit.Sigma11
  ( prependBounds,
    prependQuantifiers,
    prependArguments,
    existentialQuantifierName,
    existentialQuantifierOutputBound,
    existentialQuantifierInputBounds,
  )
where

import Control.Lens ((%~))
import Data.List (foldl')
import Die (die)
import OSL.Types.Arity (Arity (..))
import Semicircuit.Types.Sigma11 (Bound (FieldMaxBound, TermBound), ExistentialQuantifier (Some, SomeP), Formula (And, Equal, ForAll, ForSome, Iff, Implies, LessOrEqual, Not, Or, Predicate, Top, Bottom), InputBound (..), Name, OutputBound (..), Quantifier (Existential, Universal), Term (Add, App, AppInverse, Const, IndLess, Mul), var)

prependBounds ::
  [InputBound] ->
  ExistentialQuantifier ->
  ExistentialQuantifier
prependBounds bs' (Some x n bs b) =
  Some (#arity %~ (+ Arity (length bs')) $ x) n (bs' <> bs) b
prependBounds _ (SomeP {}) =
  die "there is a compiler bug; applied prependBounds to SomeP"

prependQuantifiers :: [Quantifier] -> Formula -> Formula
prependQuantifiers qs f =
  foldl' (flip prependQuantifier) f qs

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
    Top -> Top
    Bottom -> Bottom
    ForAll x b p -> ForAll x (mapBound term b) (rec p)
    ForSome q p ->
      ForSome (mapExistentialQuantifierBounds term q) (rec p)
  where
    rec = prependArguments f xs

    term =
      \case
        App g xs' ->
          if g == f
            then App (#arity . #unArity %~ (+ length xs) $ g) ((var <$> xs) <> xs')
            else App g xs'
        AppInverse g x ->
          if g == f
            then
              die $
                "prependArguments of AppInverse f: "
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

mapExistentialQuantifierBounds ::
  (Term -> Term) ->
  (ExistentialQuantifier -> ExistentialQuantifier)
mapExistentialQuantifierBounds f =
  \case
    Some x n bs b ->
      Some x n (mapInputBound f <$> bs) (mapOutputBound f b)
    SomeP x n b0 b1 ->
      SomeP x n (mapInputBound f b0) (mapOutputBound f b1)

existentialQuantifierName :: ExistentialQuantifier -> Name
existentialQuantifierName =
  \case
    Some x _ _ _ -> x
    SomeP x _ _ _ -> x

existentialQuantifierOutputBound :: ExistentialQuantifier -> Bound
existentialQuantifierOutputBound =
  \case
    Some _ _ _ (OutputBound b) -> b
    SomeP _ _ _ (OutputBound b) -> b

existentialQuantifierInputBounds :: ExistentialQuantifier -> [InputBound]
existentialQuantifierInputBounds =
  \case
    Some _ _ ibs _ -> ibs
    SomeP _ _ ib _ -> [ib]
