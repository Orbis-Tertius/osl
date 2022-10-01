{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLabels #-}


module Halo2.LogicToArithmetic (eval) where


import qualified Data.Map as Map

import Halo2.Prelude
import qualified Halo2.Coefficient as C
import qualified Halo2.Polynomial as P
import qualified Halo2.FiniteField as F
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.LogicConstraint (LogicConstraint (..), AtomicLogicConstraint (..))
import Halo2.Types.LogicToArithmeticColumnLayout (LogicToArithmeticColumnLayout (..), TruthValueColumnIndex (..), AtomAdvice (..))
import Halo2.Types.Polynomial (Polynomial (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))


eval :: FiniteField
     -> LogicToArithmeticColumnLayout
     -> LogicConstraint
     -> Maybe Polynomial
eval f layout =
  \case
    Atom (Equals p q) -> do
      advice <- Map.lookup (Equals p q) (layout ^. #atomAdvice)
      pure $ P.times f (signPoly f advice) (eqMono advice)
    Atom (LessThan p q) -> do
      advice <- Map.lookup (LessThan p q) (layout ^. #atomAdvice)
      pure $ P.times f (signPoly f advice)
             (some f (unTruthValueColumnIndex <$> advice ^. #truthValue))
    Not p -> P.minus f P.one <$> rec p
    And p q -> P.times f <$> rec p <*> rec q
    Or p q ->
      let a = rec p
          b = rec q in
      P.plus f <$> a <*> (P.minus f <$> b <*> (P.times f <$> a <*> b))
  where
    rec = eval f layout


signPoly :: FiniteField -> AtomAdvice -> Polynomial
signPoly f advice =
  P.times f (P.constant (F.half f))
    (P.plus f (P.constant F.one)
      (P.var (PolynomialVariable
                (advice ^. #sign . #unSignColumnIndex)
                0)))


eqMono :: AtomAdvice -> Polynomial
eqMono advice =
  P.multilinearMonomial C.one
    $ flip PolynomialVariable 0 . unTruthValueColumnIndex
       <$> advice ^. #truthValue


some :: FiniteField -> [ColumnIndex] -> Polynomial
some _ [] = P.zero
some f (x:xs) =
  let a = P.var (PolynomialVariable x 0)
      b = some f xs in
  P.plus f a (P.minus f b (P.times f a b))
