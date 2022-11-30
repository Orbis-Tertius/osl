{-# LANGUAGE OverloadedLabels #-}

module Halo2.CircuitMetrics (getCircuitMetrics) where

import Halo2.Polynomial (degree)
import Halo2.Prelude
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.CircuitMetrics (CircuitMetrics (CircuitMetrics), ColumnCounts, PolynomialDegreeBound (PolynomialDegreeBound), LookupTableSize, GateConstraintCount (GateConstraintCount), LookupArgumentCount (LookupArgumentCount))
import Halo2.Types.LookupArgument (LookupArgument)

getCircuitMetrics
  :: ArithmeticCircuit
  -> CircuitMetrics
getCircuitMetrics x =
  CircuitMetrics
  (x ^. #rowCount)
  (getColumnCounts x)
  (getPolyDegreeBound x)
  (GateConstraintCount (length (x ^. #gateConstraints . #constraints)))
  (LookupArgumentCount (length (x ^. #lookupArguments . #getLookupArguments)))
  (getLookupTableSize x)

getColumnCounts :: ArithmeticCircuit -> ColumnCounts
getColumnCounts = todo

getPolyDegreeBound :: ArithmeticCircuit -> PolynomialDegreeBound
getPolyDegreeBound x =
  foldl max (x ^. #gateConstraints . #degreeBound)
    (getLookupArgumentDegree <$> (x ^. #lookupArguments . #getLookupArguments))

getLookupArgumentDegree :: LookupArgument -> PolynomialDegreeBound
getLookupArgumentDegree arg =
  PolynomialDegreeBound $
  foldl max (degree (arg ^. #gate))
    (degree . (^. #getInputExpression) . fst <$> (arg ^. #tableMap))

getLookupTableSize :: ArithmeticCircuit -> LookupTableSize
getLookupTableSize = todo

todo :: a
todo = todo
