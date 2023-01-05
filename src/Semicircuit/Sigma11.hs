{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module Semicircuit.Sigma11
  ( FromName (FromName),
    ToName (ToName),
    substitute,
    HasNames (getNames),
    HasArity (getArity),
    HasPrependBounds (prependBounds),
    prependQuantifiers,
    prependArguments,
    existentialQuantifierName,
    existentialQuantifierOutputBound,
    existentialQuantifierInputBounds,
    foldConstants,
    getInputName,
    hasFieldMaxBound,
    getUniversalQuantifierStringCardinality,
    addExistentialQuantifierToStaticContext,
    addUniversalQuantifierToStaticContext,
    addInstanceQuantifierToStaticContext,
    getStaticBound,
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Control.Lens ((^.))
import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Die (die)
import OSL.Sigma11 (HasPrependBounds (prependBounds), prependQuantifiers)
import OSL.Types.Arity (Arity (..))
import OSL.Types.Cardinality (Cardinality (Cardinality))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.Sigma11.StaticEvaluationContext (StaticBound (StaticBound), StaticEvaluationContextF (StaticEvaluationContext))
import Semicircuit.Types.Sigma11 (Bound, BoundF (FieldMaxBound, TermBound), ExistentialQuantifier, ExistentialQuantifierF (Some, SomeP), Formula, FormulaF (And, Bottom, Equal, ForAll, ForSome, Given, Iff, Implies, LessOrEqual, Not, Or, Predicate, Top), InputBound, InputBoundF (..), InstanceQuantifier, InstanceQuantifierF (Instance), Name (Name), OutputBound, OutputBoundF (..), Quantifier, QuantifierF (ForAll', ForSome', Given'), Term, TermF (Add, App, AppInverse, Const, IndLess, Max, Mul))
import Stark.Types.Scalar (integerToScalar, one, scalarToInteger, two)

newtype FromName = FromName Name

newtype ToName = ToName Name

substitute :: Functor f => FromName -> ToName -> f Name -> f Name
substitute (FromName f) (ToName t) = fmap (\x -> if x == f then t else x)

class HasNames a where
  getNames :: a -> Set Name

instance HasNames a => HasNames [a] where
  getNames = mconcat . fmap getNames

instance HasNames Term where
  getNames =
    \case
      App f xs -> Set.singleton f <> getNames xs
      AppInverse f x -> Set.singleton f <> getNames x
      Add x y -> rec x <> rec y
      Mul x y -> rec x <> rec y
      IndLess x y -> rec x <> rec y
      Max x y -> rec x <> rec y
      Const _ -> mempty
    where
      rec = getNames

instance HasNames Bound where
  getNames =
    \case
      FieldMaxBound -> mempty
      TermBound x -> getNames x

instance HasNames InputBound where
  getNames =
    \case
      NamedInputBound x b -> Set.singleton x <> getNames b
      UnnamedInputBound b -> getNames b

deriving newtype instance HasNames OutputBound

instance HasNames ExistentialQuantifier where
  getNames =
    \case
      Some x _ ibs ob -> Set.singleton x <> getNames ibs <> getNames ob
      SomeP x _ ib ob -> Set.singleton x <> getNames ib <> getNames ob

instance HasNames Quantifier where
  getNames =
    \case
      ForSome' q -> getNames q
      ForAll' x b -> Set.singleton x <> getNames b
      Given' (Instance x _ ibs ob) -> Set.singleton x <> getNames ibs <> getNames ob

instance HasNames Formula where
  getNames =
    \case
      Equal x y -> getNames x <> getNames y
      LessOrEqual x y -> getNames x <> getNames y
      Predicate _ xs -> getNames xs
      Not p -> rec p
      And p q -> rec p <> rec q
      Or p q -> rec p <> rec q
      Implies p q -> rec p <> rec q
      Iff p q -> rec p <> rec q
      ForAll x b p -> Set.singleton x <> getNames b <> rec p
      ForSome q p -> getNames q <> rec p
      Given x _ ibs ob p -> Set.singleton x <> getNames ibs <> getNames ob <> rec p
      Top -> mempty
      Bottom -> mempty
    where
      rec = getNames

class HasArity a where
  getArity :: a -> Arity

instance HasArity ExistentialQuantifier where
  getArity (Some _ _ ibs _) = Arity (length ibs)
  getArity (SomeP {}) = 1

instance HasArity Quantifier where
  getArity (ForAll' {}) = 0
  getArity (ForSome' q) = getArity q
  getArity (Given' (Instance _ _ ibs _)) = Arity (length ibs)

-- Prepends the given arguments to all applications
-- of the given name. This substitution does not need
-- to account for name shadowing, since all gensyms
-- are globally unique.
prependArguments :: Name -> [Term] -> Formula -> Formula
prependArguments _ [] = id
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

getInputName :: InputBound -> Maybe Name
getInputName (NamedInputBound x _) = Just x
getInputName (UnnamedInputBound _) = Nothing

hasFieldMaxBound :: Quantifier -> Bool
hasFieldMaxBound =
  \case
    ForAll' _ b -> bound' b
    ForSome' (Some _ _ ibs ob) ->
      inputBounds ibs || outputBound ob
    ForSome' (SomeP _ _ ib ob) ->
      inputBound ib || outputBound ob
    Given' (Instance _ _ ibs ob) ->
      inputBounds ibs || outputBound ob
  where
    inputBounds :: [InputBound] -> Bool
    inputBounds = any inputBound

    inputBound :: InputBound -> Bool
    inputBound = bound' . (^. #bound)

    outputBound :: OutputBound -> Bool
    outputBound = bound' . (^. #unOutputBound)

    bound' :: Bound -> Bool
    bound' FieldMaxBound = True
    bound' (TermBound _) = False

getUniversalQuantifierStringCardinality ::
  ann ->
  StaticEvaluationContextF Name ->
  [(Name, Bound)] ->
  Either (ErrorMessage ann) Cardinality
getUniversalQuantifierStringCardinality ann ec us =
  snd <$> foldM f (ec, 1) us
  where
    f (ec', n) u = do
      ec'' <- addUniversalQuantifierToStaticContext ann ec' u
      m <- getUniversalQuantifierCardinality ann ec' u
      pure (ec'', n * m)

getUniversalQuantifierCardinality ::
  ann ->
  StaticEvaluationContextF Name ->
  (Name, Bound) ->
  Either (ErrorMessage ann) Cardinality
getUniversalQuantifierCardinality ann ec (_, b) = do
  StaticBound sb <- getStaticBound ann ec b
  case sb of
    Nothing ->
      Left (ErrorMessage ann "unbounded universal quantifier")
    Just sb' -> pure (Cardinality (scalarToInteger sb'))

addExistentialQuantifierToStaticContext ::
  ann ->
  StaticEvaluationContextF Name ->
  ExistentialQuantifier ->
  Either (ErrorMessage ann) (StaticEvaluationContextF Name)
addExistentialQuantifierToStaticContext ann ec =
  \case
    Some v _ _ (OutputBound b) -> do
      sb <- getStaticBound ann ec b
      pure (ec <> StaticEvaluationContext (Map.singleton v sb))
    SomeP v _ _ (OutputBound b) -> do
      sb <- getStaticBound ann ec b
      pure (ec <> StaticEvaluationContext (Map.singleton v sb))

addUniversalQuantifierToStaticContext ::
  ann ->
  StaticEvaluationContextF Name ->
  (Name, Bound) ->
  Either (ErrorMessage ann) (StaticEvaluationContextF Name)
addUniversalQuantifierToStaticContext ann ec (v, b) = do
  sb <- getStaticBound ann ec b
  pure (ec <> StaticEvaluationContext (Map.singleton v sb))

addInstanceQuantifierToStaticContext ::
  ann ->
  StaticEvaluationContextF Name ->
  InstanceQuantifier ->
  Either (ErrorMessage ann) (StaticEvaluationContextF Name)
addInstanceQuantifierToStaticContext ann ec (Instance v _ _ (OutputBound b)) = do
  sb <- getStaticBound ann ec b
  pure (ec <> StaticEvaluationContext (Map.singleton v sb))

getStaticBound ::
  ann ->
  StaticEvaluationContextF Name ->
  Bound ->
  Either (ErrorMessage ann) StaticBound
getStaticBound ann ec =
  \case
    FieldMaxBound -> pure (StaticBound Nothing)
    TermBound b -> getTermStaticBound ann ec b

getTermStaticBound ::
  ann ->
  StaticEvaluationContextF Name ->
  Term ->
  Either (ErrorMessage ann) StaticBound
getTermStaticBound ann ec =
  \case
    Const x -> pure . StaticBound $ (Group.+ one) <$> integerToScalar x
    App x _ -> nameBound x
    AppInverse x _ -> nameBound x
    Add x y -> (Group.+) <$> rec x <*> rec y
    Mul x y -> (Ring.*) <$> rec x <*> rec y
    IndLess {} -> pure (StaticBound (Just two))
    Max x y -> max <$> rec x <*> rec y
  where
    rec = getTermStaticBound ann ec

    nameBound x =
      case Map.lookup x (ec ^. #unStaticEvaluationContext) of
        Just b -> pure b
        Nothing -> Left (ErrorMessage ann "name lookup failed")
