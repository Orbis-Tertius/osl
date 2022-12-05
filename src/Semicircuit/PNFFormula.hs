{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Semicircuit.PNFFormula
  ( toPNFFormula,
    toSemicircuit,
  )
where

import Control.Lens ((^.))
import Data.Set (Set)
import qualified Data.Set as Set
import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (existentialQuantifierName)
import qualified Semicircuit.Types.PNFFormula as PNF
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Semicircuit (FreeVariables (..), Semicircuit (..))
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
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [] [PNF.All x b] []
      pure (PNF.Formula a' (qNew <> aq))
    S11.ForSome (S11.Some x c bs b) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.Some x c bs b] [] []
      pure $ PNF.Formula a' (qNew <> aq)
    S11.ForSome (S11.SomeP x c b0 b1) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.SomeP x c b0 b1] [] []
      pure $ PNF.Formula a' (qNew <> aq)
    S11.Given x n ibs ob a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [] [] [PNF.Instance x n ibs ob]
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

freeVariables :: PNF.Formula -> FreeVariables
freeVariables (PNF.Formula qf qs) =
  FreeVariables (Set.difference (allVariables qf) (quantifiedVariables qs))

quantifiedVariables :: PNF.Quantifiers -> Set S11.Name
quantifiedVariables (PNF.Quantifiers es us gs) =
  Set.fromList (existentialQuantifierName <$> es)
    <> Set.fromList ((^. #name) <$> us)
    <> Set.fromList ((^. #name) <$> gs)

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
        S11.Max x y -> term x <> term y
        S11.Const _ -> mempty

-- Turns a PNF formula into a semicircuit.
toSemicircuit :: PNF.Formula -> Semicircuit
toSemicircuit f = Semicircuit (freeVariables f) f
