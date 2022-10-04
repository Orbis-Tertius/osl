{-# LANGUAGE LambdaCase #-}


module Semicircuit.PNFFormula
  ( toPrenexNormalForm
  ) where


import qualified OSL.Types.Sigma11 as S11
import qualified Semicircuit.Types.PNFFormula as PNF
import qualified Semicircuit.Types.QFFormula as QF


toPrenexNormalForm :: S11.Formula -> PNF.Formula
toPrenexNormalForm =
  \case
    S11.Equal a b -> PNF.Formula (QF.Equal a b) mempty
    S11.LessOrEqual a b -> PNF.Formula (QF.LessOrEqual a b) mempty
    S11.And a b -> rec' QF.And a b
    S11.Or a b -> rec' QF.Or a b
    S11.Not a ->
      let PNF.Formula a' q = rec a
      in PNF.Formula (QF.Not a') q
    S11.Implies a b -> rec' QF.Implies a b
    S11.Iff a b -> rec' QF.Iff a b
    S11.Predicate p args ->
      PNF.Formula (QF.Predicate p args) mempty
    S11.ForAll b a ->
      let PNF.Formula a' aq = rec a
          qNew = PNF.Quantifiers [] [PNF.ForAll b] []
          aq' = incrementPrecedingUniQs aq
      in PNF.Formula a' (qNew <> aq')
    S11.Exists (S11.ExistsFO b) a ->
      let PNF.Formula a' aq = rec a
          qNew = PNF.Quantifiers [PNF.Exists b 0] [] []
      in PNF.Formula a' (qNew <> aq)
    S11.Exists (S11.ExistsSO c b bs) a ->
      let PNF.Formula a' aq = rec a
          qNew = PNF.Quantifiers [] [] [PNF.ExistsF c b bs 0]
      in PNF.Formula a' (qNew <> aq)
    S11.Exists (S11.ExistsP c b0 b1) a ->
      let PNF.Formula a' aq = rec a
          qNew = PNF.Quantifiers [] [] [PNF.ExistsP c b0 b1 0]
      in PNF.Formula a' (qNew <> aq)
  where
    rec = toPrenexNormalForm

    rec' f a b =
      let PNF.Formula a' aq = rec a
          PNF.Formula b' bq = rec b
      in PNF.Formula (f a' b') (aq <> bq)


incrementPrecedingUniQs :: PNF.Quantifiers -> PNF.Quantifiers
incrementPrecedingUniQs (PNF.Quantifiers foE foU so) =
  PNF.Quantifiers (f <$> foE) foU (g <$> so)
  where
    f :: PNF.FOExistsQ -> PNF.FOExistsQ
    f (PNF.Exists b n) = PNF.Exists b (n+1)

    g :: PNF.SOExistsQ -> PNF.SOExistsQ
    g (PNF.ExistsF c b bs n) = PNF.ExistsF c b bs (n+1)
    g (PNF.ExistsP c b0 b1 n) = PNF.ExistsP c b0 b1 (n+1)
