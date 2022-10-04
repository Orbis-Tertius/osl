{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module Semicircuit.PNFFormula
  ( toPNFFormula
  ) where


import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NonEmpty

import OSL.Sigma11 (incrementDeBruijnIndices)
import OSL.Types.Arity (Arity (..))
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.Sigma11 as S11
import qualified Semicircuit.Types.PNFFormula as PNF
import qualified Semicircuit.Types.QFFormula as QF


-- TODO: Let's assume that the input formula is already
-- in prenex normal form
toPNFFormula :: ann -> S11.Formula -> Either (ErrorMessage ann) PNF.Formula
toPNFFormula ann =
  \case
    S11.Equal a b -> pure $ PNF.Formula (QF.Equal a b) mempty
    S11.LessOrEqual a b -> pure $ PNF.Formula (QF.LessOrEqual a b) mempty
    S11.And a b -> rec' QF.And a b
    S11.Or a b -> rec' QF.Or a b
    S11.Not a -> do
      -- TODO this is wrong; quantifier types flip
      PNF.Formula a' q <- rec a
      pure $ PNF.Formula (QF.Not a') q
    -- TODO this is wrong; a quantifier types flip
    S11.Implies a b -> rec' QF.Implies a b
    -- TODO this is wrong
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
      let a'' = moveDeBruijnIndices bq a'
      pure $ PNF.Formula (f a'' b') (aq <> bq)


-- Increment de Bruijn indices in a to account for inserting
-- innerQs before all quantifiers that a was surrounded by.
moveDeBruijnIndices
  :: PNF.Quantifiers
  -> QF.Formula
  -> QF.Formula
moveDeBruijnIndices innerQs@(PNF.Quantifiers _ _ so) a =
  let arities :: Set Arity
      arities = Set.fromList $ [0] <> (qArity <$> so)

      counts :: [(Arity, Int)]
      counts = countQs innerQs <$> Set.toList arities

      fs :: [QF.Formula -> QF.Formula]
      fs = uncurry incrementDeBruijnIndices <$> counts

  in foldl (.) id fs $ a


qArity :: PNF.SOExistsQ -> Arity
qArity =
  \case
    PNF.ExistsF _ _ bs -> Arity $ NonEmpty.length bs
    PNF.ExistsP _ _ _ -> Arity 1


countQs :: PNF.Quantifiers -> Arity -> (Arity, Int)
countQs (PNF.Quantifiers foExists foUni so) n =
  if n == 0
  then (n, length foExists + length foUni)
  else (n, length (filter ((== n) . qArity) so))


incrementPrecedingUniQs :: PNF.Quantifiers -> PNF.Quantifiers
incrementPrecedingUniQs (PNF.Quantifiers foE foU so) =
  PNF.Quantifiers (f <$> foE) foU (g <$> so)
  where
    f :: PNF.FOExistsQ -> PNF.FOExistsQ
    f (PNF.Exists b n) = PNF.Exists b (n+1)

    g :: PNF.SOExistsQ -> PNF.SOExistsQ
    g (PNF.ExistsF c b bs) = PNF.ExistsF c b bs
    g (PNF.ExistsP c b0 b1) = PNF.ExistsP c b0 b1
