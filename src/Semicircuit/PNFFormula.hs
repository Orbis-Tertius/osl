{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module Semicircuit.PNFFormula
  ( toPNFFormula
  ) where


import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.Sigma11 as S11
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
    S11.ForAll b a -> do
      PNF.Formula a' aq <- rec a
      case aq of
        PNF.Quantifiers _ _ [] -> do
          let qNew = PNF.Quantifiers [] [PNF.ForAll b] []
              aq' = incrementPrecedingUniQs aq
          pure $ PNF.Formula a' (qNew <> aq')
        _ -> Left . ErrorMessage ann $
          "second-order quantifier inside a first-order universal quantifier"
    S11.Exists (S11.ExistsFO b) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [PNF.Exists b 0] [] []
      pure $ PNF.Formula a' (qNew <> aq)
    S11.Exists (S11.ExistsSO c b bs) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [] [] [PNF.ExistsF c b bs]
      pure $ PNF.Formula a' (qNew <> aq)
    S11.Exists (S11.ExistsP c b0 b1) a -> do
      PNF.Formula a' aq <- rec a
      let qNew = PNF.Quantifiers [] [] [PNF.ExistsP c b0 b1]
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


incrementPrecedingUniQs :: PNF.Quantifiers -> PNF.Quantifiers
incrementPrecedingUniQs (PNF.Quantifiers foE foU so) =
  PNF.Quantifiers (f <$> foE) foU (g <$> so)
  where
    f :: PNF.FOExistsQ -> PNF.FOExistsQ
    f (PNF.Exists b n) = PNF.Exists b (n+1)

    g :: PNF.SOExistsQ -> PNF.SOExistsQ
    g (PNF.ExistsF c b bs) = PNF.ExistsF c b bs
    g (PNF.ExistsP c b0 b1) = PNF.ExistsP c b0 b1
