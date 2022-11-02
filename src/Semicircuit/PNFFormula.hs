{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Semicircuit.PNFFormula
  ( toPNFFormula,
    indicatorFunctionCalls,
    functionCalls,
    toSemicircuit,
  )
where

import Control.Lens ((^.))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Set (Set)
import qualified Data.Set as Set
import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (existentialQuantifierName, prependBounds)
import qualified Semicircuit.Types.PNFFormula as PNF
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Semicircuit (AdviceTerms (..), FreeVariables (..), FunctionCall (..), FunctionCalls (..), IndicatorFunctionCall (..), IndicatorFunctionCalls (..), Semicircuit (..))
import qualified Semicircuit.Types.Sigma11 as S11

-- Turns a strong prenex normal form into a PNF formula.
toPNFFormula ::
  ann ->
  S11.Formula ->
  Either (ErrorMessage ann) PNF.Formula
toPNFFormula ann =
  \case
    S11.Equal a b -> pure $ PNF.Formula (QF.Equal a b) mempty
    S11.LessOrEqual a b -> pure $ PNF.Formula (QF.LessOrEqual a b) mempty
    S11.Top -> pure $ PNF.Formula QF.Top mempty
    S11.Bottom -> pure $ PNF.Formula QF.Bottom mempty
    S11.And a b -> rec' QF.And a b
    S11.Or a b -> rec' QF.Or a b
    S11.Not a -> do
      PNF.Formula a' q <- rec a
      if q == mempty
        then pure $ PNF.Formula (QF.Not a') mempty
        else
          Left . ErrorMessage ann $
            "input formula is not a prenex normal form"
    S11.Implies a b -> rec' QF.Implies a b
    S11.Iff a b -> rec' QF.Iff a b
    S11.Predicate p args ->
      pure $ PNF.Formula (QF.Predicate p args) mempty
    S11.ForAll x b a -> do
      PNF.Formula a' (PNF.Quantifiers aqE aqU aqG) <-
        rec a
      let qNew = PNF.Quantifiers [] [PNF.All x b] []
          aq' =
            PNF.Quantifiers
              ( prependBounds [S11.InputBound x b]
                  <$> aqE
              )
              aqU
              aqG
      pure (PNF.Formula a' (qNew <> aq'))
    S11.ForSome (S11.Some x c bs b) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.Some x c bs b] [] []
      pure $ PNF.Formula a' (qNew <> aq)
    S11.ForSome (S11.SomeP x c b0 b1) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.SomeP x c b0 b1] [] []
      pure $ PNF.Formula a' (qNew <> aq)
    S11.Given x ibs ob a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [] [] [PNF.Instance x ibs ob]
      pure $ PNF.Formula a' (qNew <> aq)
  where
    rec = toPNFFormula ann

    rec' f a b = do
      PNF.Formula a' aq <- rec a
      PNF.Formula b' bq <- rec b
      if aq == mempty && bq == mempty
        then pure $ PNF.Formula (f a' b') mempty
        else
          Left . ErrorMessage ann $
            "input formula is not a prenex normal form"

-- Gets the indicator function calls in the given PNF formula.
indicatorFunctionCalls :: PNF.Formula -> IndicatorFunctionCalls
indicatorFunctionCalls (PNF.Formula qf (PNF.Quantifiers es us gs)) =
  qff qf <> mconcat (eQ <$> es) <> mconcat (uQ <$> us) <> mconcat (gQ <$> gs)
  where
    qff :: QF.Formula -> IndicatorFunctionCalls
    qff =
      \case
        QF.Equal x y -> term x <> term y
        QF.LessOrEqual x y -> term x <> term y
        QF.Predicate _ xs -> mconcat $ term <$> xs
        QF.Not p -> qff p
        QF.And p q -> qff p <> qff q
        QF.Or p q -> qff p <> qff q
        QF.Implies p q -> qff p <> qff q
        QF.Iff p q -> qff p <> qff q
        QF.Top -> mempty
        QF.Bottom -> mempty

    eQ ::
      PNF.ExistentialQuantifier ->
      IndicatorFunctionCalls
    eQ =
      \case
        S11.Some _ _ inBounds outBound ->
          mconcat (bound . (^. #bound) <$> inBounds)
            <> bound (outBound ^. #unOutputBound)
        S11.SomeP _ _ inBound outBound ->
          bound (inBound ^. #bound)
            <> bound (outBound ^. #unOutputBound)

    uQ ::
      PNF.UniversalQuantifier ->
      IndicatorFunctionCalls
    uQ (PNF.All _ b) = bound b

    gQ :: PNF.InstanceQuantifier -> IndicatorFunctionCalls
    gQ (PNF.Instance _ inBounds outBound) =
      mconcat (bound . (^. #bound) <$> inBounds)
        <> bound (outBound ^. #unOutputBound)

    bound ::
      S11.Bound ->
      IndicatorFunctionCalls
    bound =
      \case
        S11.TermBound x -> term x
        S11.FieldMaxBound -> mempty

    term ::
      S11.Term ->
      IndicatorFunctionCalls
    term =
      \case
        S11.App _ xs -> mconcat (term <$> xs)
        S11.AppInverse _ x -> term x
        S11.Add x y -> term x <> term y
        S11.Mul x y -> term x <> term y
        S11.IndLess x y ->
          term x
            <> term y
            <> IndicatorFunctionCalls (Set.singleton (IndicatorFunctionCall x y))
        S11.Const _ -> mempty

functionCalls :: PNF.Formula -> FunctionCalls
functionCalls (PNF.Formula qf (PNF.Quantifiers es us gs)) =
  qff qf <> mconcat (eQ <$> es) <> mconcat (uQ <$> us) <> mconcat (gQ <$> gs)
  where
    qff :: QF.Formula -> FunctionCalls
    qff =
      \case
        QF.Equal x y -> term x <> term y
        QF.LessOrEqual x y -> term x <> term y
        QF.Predicate _ xs -> mconcat $ term <$> xs
        QF.Not p -> qff p
        QF.And p q -> qff p <> qff q
        QF.Or p q -> qff p <> qff q
        QF.Implies p q -> qff p <> qff q
        QF.Iff p q -> qff p <> qff q
        QF.Top -> mempty
        QF.Bottom -> mempty

    eQ ::
      PNF.ExistentialQuantifier ->
      FunctionCalls
    eQ =
      \case
        S11.Some _ _ inBounds outBound ->
          mconcat (bound . (^. #bound) <$> inBounds)
            <> bound (outBound ^. #unOutputBound)
        S11.SomeP _ _ inBound outBound ->
          bound (inBound ^. #bound)
            <> bound (outBound ^. #unOutputBound)

    uQ ::
      PNF.UniversalQuantifier ->
      FunctionCalls
    uQ (PNF.All _ b) = bound b

    gQ :: PNF.InstanceQuantifier -> FunctionCalls
    gQ (PNF.Instance _ ibs ob) =
      mconcat (bound . (^. #bound) <$> ibs) <> bound (ob ^. #unOutputBound)

    bound ::
      S11.Bound ->
      FunctionCalls
    bound =
      \case
        S11.TermBound x -> term x
        S11.FieldMaxBound -> mempty

    term ::
      S11.Term ->
      FunctionCalls
    term =
      \case
        S11.App f xs ->
          mconcat (term <$> xs)
            <> ( case NonEmpty.nonEmpty xs of
                   Just xs' -> FunctionCalls (Set.singleton (FunctionCall f xs'))
                   Nothing -> mempty
               )
        S11.AppInverse f x ->
          term x
            <> FunctionCalls (Set.singleton (FunctionCall f [x])) -- TODO: invert
        S11.Add x y -> term x <> term y
        S11.Mul x y -> term x <> term y
        S11.IndLess x y -> term x <> term y
        S11.Const _ -> mempty

indicatorFunctionCallsArguments ::
  IndicatorFunctionCalls -> AdviceTerms
indicatorFunctionCallsArguments =
  mconcat . fmap indicatorFunctionCallArguments
    . Set.toList
    . unIndicatorFunctionCalls

indicatorFunctionCallArguments ::
  IndicatorFunctionCall -> AdviceTerms
indicatorFunctionCallArguments (IndicatorFunctionCall x y) =
  AdviceTerms [x, y]

functionCallsArguments :: FunctionCalls -> AdviceTerms
functionCallsArguments =
  mconcat . fmap functionCallArguments . Set.toList . unFunctionCalls

functionCallArguments :: FunctionCall -> AdviceTerms
functionCallArguments (FunctionCall _ ts) =
  AdviceTerms (Set.fromList (NonEmpty.toList ts))

freeVariables :: PNF.Formula -> FreeVariables
freeVariables (PNF.Formula qf qs) =
  FreeVariables (Set.difference (allVariables qf) (quantifiedVariables qs))

quantifiedVariables :: PNF.Quantifiers -> Set S11.Name
quantifiedVariables (PNF.Quantifiers es us _gs) =
  Set.fromList (existentialQuantifierName <$> es)
    <> Set.fromList ((^. #name) <$> us)

allVariables :: QF.Formula -> Set S11.Name
allVariables =
  \case
    QF.Equal a b -> term a <> term b
    QF.LessOrEqual a b -> term a <> term b
    QF.Predicate _ xs -> mconcat (term <$> xs)
    QF.Not p -> rec p
    QF.And p q -> rec p <> rec q
    QF.Or p q -> rec p <> rec q
    QF.Implies p q -> rec p <> rec q
    QF.Iff p q -> rec p <> rec q
    QF.Top -> mempty
    QF.Bottom -> mempty
  where
    rec = allVariables

    term :: S11.Term -> Set S11.Name
    term =
      \case
        S11.App f xs -> [f] <> mconcat (term <$> xs)
        S11.AppInverse f x -> [f] <> term x
        S11.Add x y -> term x <> term y
        S11.Mul x y -> term x <> term y
        S11.IndLess x y -> term x <> term y
        S11.Const _ -> mempty

-- Turns a PNF formula into a semicircuit.
toSemicircuit :: PNF.Formula -> Semicircuit
toSemicircuit f =
  let fvs = freeVariables f
      ifs = indicatorFunctionCalls f
      fs = functionCalls f
      ts =
        AdviceTerms
          ( Set.fromList
              ( functionCallToTerm
                  <$> Set.toList (unFunctionCalls fs)
              )
          )
          <> indicatorFunctionCallsArguments ifs
          <> functionCallsArguments fs
   in Semicircuit fvs ifs fs ts f

functionCallToTerm :: FunctionCall -> S11.Term
functionCallToTerm (FunctionCall f xs) =
  S11.App f (NonEmpty.toList xs)
