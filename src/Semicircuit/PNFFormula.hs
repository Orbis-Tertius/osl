{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module Semicircuit.PNFFormula
  ( toPNFFormula
  ) where


import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (prependBounds)
import qualified Semicircuit.Types.Sigma11 as S11
import qualified Semicircuit.Types.PNFFormula as PNF
import qualified Semicircuit.Types.QFFormula as QF


toPNFFormula :: ann -> S11.Formula -> Either (ErrorMessage ann) PNF.Formula
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
       else Left . ErrorMessage ann
          $ "input formula is not a prenex normal form"
    S11.Implies a b -> rec' QF.Implies a b
    S11.Iff a b -> rec' QF.Iff a b
    S11.Predicate p args ->
      pure $ PNF.Formula (QF.Predicate p args) mempty
    S11.ForAll x b a -> do
      PNF.Formula a' (PNF.Quantifiers aqE aqU)
        <- rec a
      let qNew = PNF.Quantifiers [] [PNF.All x b]
          aq' = PNF.Quantifiers
            (prependBounds [S11.InputBound x b]
              <$> aqE)
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
        else Left . ErrorMessage ann
          $ "input formula is not a prenex normal form"
