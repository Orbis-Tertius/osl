{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}

module Halo2.CircuitMetrics (getCircuitMetrics) where

import Control.Lens ((<&>))
import Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Halo2.Circuit (getPolynomialVariables)
import Halo2.Polynomial (degree)
import Halo2.Prelude
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.CircuitMetrics (CircuitMetrics (CircuitMetrics), ColumnClass (Advice, All, EqualityConstrainable, Fixed, Instance), ColumnCount (ColumnCount), ColumnCounts (ColumnCounts), GateConstraintCount (GateConstraintCount), LookupArgumentCount (LookupArgumentCount), LookupTableSize (LookupTableSize), PolynomialDegreeBound (PolynomialDegreeBound), RowOffsetMagnitude (RowOffsetMagnitude))
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType)
import qualified Halo2.Types.ColumnType as CT
import Halo2.Types.LookupArgument (LookupArgument)
import Halo2.Types.Polynomial (Polynomial)

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
    (getRowOffsetMagnitude x)

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
    ( getLookupArgumentDegree
        <$> Set.toList (x ^. #lookupArguments . #getLookupArguments)
    )

getLookupArgumentDegree :: LookupArgument Polynomial -> PolynomialDegreeBound
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
    ( getLookupArgumentTableSize
        <$> Set.toList (x ^. #lookupArguments . #getLookupArguments)
    )

getLookupArgumentTableSize :: LookupArgument a -> LookupTableSize
getLookupArgumentTableSize arg =
  LookupTableSize (length (arg ^. #tableMap))

getRowOffsetMagnitude :: ArithmeticCircuit -> RowOffsetMagnitude
getRowOffsetMagnitude c =
  foldl' max 0 $
    Set.toList (getPolynomialVariables c)
      <&> RowOffsetMagnitude . abs . (^. #rowIndex . #getRowIndex)
