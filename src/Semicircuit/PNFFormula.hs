{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
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
import qualified Data.Set as Set
import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (prependBounds)
import qualified Semicircuit.Types.PNFFormula as PNF
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Semicircuit (FunctionCall (..), FunctionCalls (..), IndicatorFunctionCall (..), IndicatorFunctionCalls (..), Semicircuit (..), AdviceTerms (..))
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
      PNF.Formula a' (PNF.Quantifiers aqE aqU) <-
        rec a
      let qNew = PNF.Quantifiers [] [PNF.All x b]
          aq' =
            PNF.Quantifiers
              ( prependBounds [S11.InputBound x b]
                  <$> aqE
              )
              aqU
      pure (PNF.Formula a' (qNew <> aq'))
    S11.ForSome (S11.Some x c bs b) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.Some x c bs b] []
      pure $ PNF.Formula a' (qNew <> aq)
    S11.ForSome (S11.SomeP x c b0 b1) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.SomeP x c b0 b1] []
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
indicatorFunctionCalls (PNF.Formula qf (PNF.Quantifiers es us)) =
  qff qf <> mconcat (eQ <$> es) <> mconcat (uQ <$> us)
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
functionCalls (PNF.Formula qf (PNF.Quantifiers es us)) =
  qff qf <> mconcat (eQ <$> es) <> mconcat (uQ <$> us)
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
        S11.AppInverse _ x -> term x
        S11.Add x y -> term x <> term y
        S11.Mul x y -> term x <> term y
        S11.IndLess x y -> term x <> term y
        S11.Const _ -> mempty

indicatorFunctionCallsArguments
  :: IndicatorFunctionCalls
  -> AdviceTerms
indicatorFunctionCallsArguments = todo

functionCallsArguments
  :: FunctionCalls
  -> AdviceTerms
functionCallsArguments = todo

boundsTerms :: PNF.Quantifiers -> AdviceTerms
boundsTerms = todo

todo :: a
todo = todo

-- Turns a PNF formula into a semicircuit.
toSemicircuit :: PNF.Formula -> Semicircuit
toSemicircuit f =
  let ifs = indicatorFunctionCalls f
      fs = functionCalls f
      ts = indicatorFunctionCallsArguments ifs
        <> functionCallsArguments fs
        <> boundsTerms (f ^. #quantifiers)
  in Semicircuit ifs fs ts f
