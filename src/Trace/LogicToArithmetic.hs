{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Trace.LogicToArithmetic
  ( logicCircuitToArithmeticCircuit
  ) where

import Halo2.AIR (fromCircuit)
import Halo2.Prelude
import Halo2.Types.Circuit (LogicCircuit, ArithmeticCircuit)
import Trace.FromLogicAIR (logicAIRToTraceType)
import Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit)

logicCircuitToArithmeticCircuit
  :: LogicCircuit
  -> ArithmeticCircuit
logicCircuitToArithmeticCircuit lc =
  traceTypeToArithmeticCircuit
  (logicAIRToTraceType (fromCircuit lc))
  (lc ^. #equalityConstrainableColumns)
  (lc ^. #lookupArguments) -- TODO: do these change in any way?
  (lc ^. #equalityConstraints)
