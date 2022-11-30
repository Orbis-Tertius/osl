{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}

module Halo2.CircuitMetrics (getCircuitMetrics) where

import Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Halo2.Polynomial (degree)
import Halo2.Prelude
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.CircuitMetrics (CircuitMetrics (CircuitMetrics), ColumnClass (Advice, All, EqualityConstrainable, Fixed, Instance), ColumnCount (ColumnCount), ColumnCounts (ColumnCounts), GateConstraintCount (GateConstraintCount), LookupArgumentCount (LookupArgumentCount), LookupTableSize (LookupTableSize), PolynomialDegreeBound (PolynomialDegreeBound))
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType)
import qualified Halo2.Types.ColumnType as CT
import Halo2.Types.LookupArgument (LookupArgument)

getCircuitMetrics ::
  ArithmeticCircuit ->
  CircuitMetrics
getCircuitMetrics x =
  CircuitMetrics
    (x ^. #rowCount)
    (getColumnCounts x)
    (getPolyDegreeBound x)
    (GateConstraintCount (length (x ^. #gateConstraints . #constraints)))
    (LookupArgumentCount (length (x ^. #lookupArguments . #getLookupArguments)))
    (getLookupTableSize x)

getColumnCounts :: ArithmeticCircuit -> ColumnCounts
getColumnCounts x =
  ColumnCounts
    (ColumnCount @Advice (Map.size (Map.filter (== CT.Advice) colTypes)))
    (ColumnCount @Instance (Map.size (Map.filter (== CT.Instance) colTypes)))
    (ColumnCount @Fixed (Map.size (Map.filter (== CT.Fixed) colTypes)))
    (ColumnCount @All (Map.size colTypes))
    (ColumnCount @EqualityConstrainable (Set.size (x ^. #equalityConstrainableColumns . #getEqualityConstrainableColumns)))
  where
    colTypes :: Map ColumnIndex ColumnType
    colTypes = x ^. #columnTypes . #getColumnTypes

getPolyDegreeBound :: ArithmeticCircuit -> PolynomialDegreeBound
getPolyDegreeBound x =
  foldl'
    max
    (x ^. #gateConstraints . #degreeBound)
    (getLookupArgumentDegree <$> (x ^. #lookupArguments . #getLookupArguments))

getLookupArgumentDegree :: LookupArgument -> PolynomialDegreeBound
getLookupArgumentDegree arg =
  PolynomialDegreeBound $
    foldl'
      max
      (degree (arg ^. #gate))
      (degree . (^. #getInputExpression) . fst <$> (arg ^. #tableMap))

getLookupTableSize :: ArithmeticCircuit -> LookupTableSize
getLookupTableSize x =
  foldl'
    max
    0
    (getLookupArgumentTableSize <$> (x ^. #lookupArguments . #getLookupArguments))

getLookupArgumentTableSize :: LookupArgument -> LookupTableSize
getLookupArgumentTableSize arg =
  LookupTableSize (length (arg ^. #tableMap))
