{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Trace.LogicToArithmetic
  ( logicCircuitToArithmeticCircuit
  ) where

import Halo2.AIR (fromCircuit)
import Halo2.Prelude
import Halo2.Types.Circuit (LogicCircuit, ArithmeticCircuit)
import Halo2.Types.LookupArguments (LookupArguments)
import Trace.FromLogicAIR (logicAIRToTraceType)
import Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit)

logicCircuitToArithmeticCircuit
  :: LogicCircuit
  -> ArithmeticCircuit
logicCircuitToArithmeticCircuit lc =
  traceTypeToArithmeticCircuit
  (logicAIRToTraceType (fromCircuit lc))
  (lc ^. #equalityConstrainableColumns)
  (lookupArguments lc)
  (lc ^. #equalityConstraints)

-- Each lookup argument in the logic circuit results in a
-- step type, and a lookup argument, gated to the step type
-- corresponding, which is the same lookup argument with the
-- column indices substituted for input and output column
-- indices in the trace type.
lookupArguments
  :: LogicCircuit
  -> LookupArguments
lookupArguments = todo

todo :: a
todo = todo
