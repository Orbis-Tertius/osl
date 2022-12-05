{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module Semicircuit.Sigma11
  ( MapNames (mapNames),
    FromName (FromName),
    ToName (ToName),
    substitute,
    HasNames (getNames),
    HasArity (getArity),
    prependBounds,
    prependQuantifiers,
    prependArguments,
    existentialQuantifierName,
    existentialQuantifierOutputBound,
    existentialQuantifierInputBounds,
    foldConstants,
  )
where

import Control.Lens ((%~), (^.))
import Data.List (foldl')
import Data.Set (Set)
import Die (die)
import OSL.Types.Arity (Arity (..))
import Semicircuit.Types.Sigma11 (Bound (FieldMaxBound, TermBound), ExistentialQuantifier (Some, SomeP), Formula (And, Bottom, Equal, ForAll, ForSome, Given, Iff, Implies, LessOrEqual, Not, Or, Predicate, Top), InputBound (..), Name (Name), OutputBound (..), Quantifier (Existential, Instance, Universal), Term (Add, App, AppInverse, Const, IndLess, Max, Mul))

class MapNames a where
  mapNames :: (Name -> Name) -> a -> a

instance MapNames Name where
  mapNames = id

instance MapNames Term where
  mapNames f =
    \case
      App g xs -> App (f g) (rec <$> xs)
      AppInverse g x -> AppInverse (f g) (rec x)
      Add x y -> Add (rec x) (rec y)
      Mul x y -> Mul (rec x) (rec y)
      IndLess x y -> IndLess (rec x) (rec y)
      Max x y -> Max (rec x) (rec y)
      Const x -> Const x
    where
      rec = mapNames f

instance MapNames Bound where
  mapNames f =
    \case
      FieldMaxBound -> FieldMaxBound
      TermBound x -> TermBound (mapNames f x)

instance MapNames InputBound where
  mapNames f (NamedInputBound x b) =
    NamedInputBound (f x) (mapNames f b)
  mapNames f (UnnamedInputBound b) =
    UnnamedInputBound (mapNames f b)

deriving newtype instance MapNames OutputBound

instance MapNames ExistentialQuantifier where
  mapNames f =
    \case
      Some x n ibs ob -> Some (f x) n (mapNames f <$> ibs) (mapNames f ob)
      SomeP x n ib ob -> SomeP (f x) n (mapNames f ib) (mapNames f ob)

instance MapNames Formula where
  mapNames f =
    \case
      Equal x y -> Equal (term x) (term y)
      LessOrEqual x y -> LessOrEqual (term x) (term y)
      Predicate p xs -> Predicate p (term <$> xs)
      And p q -> And (rec p) (rec q)
      Not p -> Not (rec p)
      Or p q -> Or (rec p) (rec q)
      Implies p q -> Implies (rec p) (rec q)
      Iff p q -> Iff (rec p) (rec q)
      ForAll x a p -> ForAll (f x) (mapNames f a) (rec p)
      ForSome q p -> ForSome (mapNames f q) (rec p)
      Given x n ibs ob p ->
        Given (f x) n (mapNames f <$> ibs) (mapNames f ob) (rec p)
      Top -> Top
      Bottom -> Bottom
    where
      rec = mapNames f
      term = mapNames f

instance MapNames Quantifier where
  mapNames f =
    \case
      Universal x b -> Universal (f x) (mapNames f b)
      Existential q -> Existential (mapNames f q)
      Instance x n ibs ob -> Instance (f x) n (mapNames f <$> ibs) (mapNames f ob)

newtype FromName = FromName Name

newtype ToName = ToName Name

substitute :: MapNames a => FromName -> ToName -> a -> a
substitute (FromName f) (ToName t) = mapNames (\x -> if x == f then t else x)

class HasNames a where
  getNames :: a -> Set Name

instance HasNames ExistentialQuantifier where
  getNames = todo

instance HasNames Quantifier where
  getNames = todo

instance HasNames Formula where
  getNames = todo

todo :: a
todo = todo

class HasArity a where
  getArity :: a -> Arity

instance HasArity ExistentialQuantifier where
  getArity (Some _ _ ibs _) = Arity (length ibs)
  getArity (SomeP {}) = 1

instance HasArity Quantifier where
  getArity (Universal {}) = 0
  getArity (Existential q) = getArity q
  getArity (Instance _ _ ibs _) = Arity (length ibs)

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
prependQuantifier (Instance x n ibs ob) f =
  Given x n ibs ob f

-- Prepends the given arguments to all applications
-- of the given name. This substitution does not need
-- to account for name shadowing, since all gensyms
-- are globally unique.
prependArguments :: Name -> [Term] -> Formula -> Formula
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
    Given x n ibs ob p ->
      Given
        x
        n
        (mapInputBound term <$> ibs)
        (mapOutputBound term ob)
        (rec p)
  where
    rec = prependArguments f xs

    term =
      \case
        App g xs' ->
          if (g ^. #sym) == (f ^. #sym)
            then
              App
                (Name ((g ^. #arity) + Arity (length xs)) (g ^. #sym))
                (xs <> (term <$> xs'))
            else App g (term <$> xs')
        AppInverse g x ->
          if (g ^. #sym) == (f ^. #sym)
            then
              die $
                "prependArguments of AppInverse f: "
                  <> "this is a compiler bug"
            else AppInverse g (term x)
        Add x y ->
          Add (term x) (term y)
        Mul x y ->
          Mul (term x) (term y)
        IndLess x y ->
          IndLess (term x) (term y)
        Max x y ->
          Max (term x) (term y)
        Const x -> Const x

mapBound :: (Term -> Term) -> Bound -> Bound
mapBound f =
  \case
    TermBound x -> TermBound (f x)
    FieldMaxBound -> FieldMaxBound

mapInputBound :: (Term -> Term) -> InputBound -> InputBound
mapInputBound f (NamedInputBound x b) =
  NamedInputBound x (mapBound f b)
mapInputBound f (UnnamedInputBound b) =
  UnnamedInputBound (mapBound f b)

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

foldConstants :: Term -> Term
foldConstants =
  \case
    App f xs -> App f (rec <$> xs)
    AppInverse f x -> AppInverse f (rec x)
    Add x y ->
      case (rec x, rec y) of
        (Const x', Const y') -> Const (x' + y')
        (x', y') -> x' `Add` y'
    Mul x y ->
      case (rec x, rec y) of
        (Const x', Const y') -> Const (x' * y')
        (x', y') -> x' `Mul` y'
    IndLess x y ->
      case (rec x, rec y) of
        (Const x', Const y') ->
          if x' < y' then Const 1 else Const 0
        (x', y') -> x' `IndLess` y'
    Max x y ->
      case (rec x, rec y) of
        (Const x', Const y') -> Const (x' `max` y')
        (x', y') -> x' `Max` y'
    Const x -> Const x
  where
    rec = foldConstants
