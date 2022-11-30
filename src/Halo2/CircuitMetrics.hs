{-# LANGUAGE OverloadedLabels #-}

module Halo2.CircuitMetrics (getCircuitMetrics) where

import Halo2.Prelude
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.CircuitMetrics (CircuitMetrics (CircuitMetrics), ColumnCounts, PolynomialDegreeBound, LookupTableSize, GateConstraintCount (GateConstraintCount), LookupArgumentCount (LookupArgumentCount))

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
getPolyDegreeBound = todo

getLookupTableSize :: ArithmeticCircuit -> LookupTableSize
getLookupTableSize = todo

todo :: a
todo = todo
