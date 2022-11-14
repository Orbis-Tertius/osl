{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Trace.LogicToArithmetic
  ( logicCircuitToArithmeticCircuit
  ) where

import Halo2.Types.Circuit (LogicCircuit, ArithmeticCircuit)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import Halo2.Types.EqualityConstraints (EqualityConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Trace.FromLogicCircuit (logicCircuitToTraceType)
import Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit)
import Trace.Types (TraceType)

logicCircuitToArithmeticCircuit
  :: LogicCircuit
  -> ArithmeticCircuit
logicCircuitToArithmeticCircuit lc =
  traceTypeToArithmeticCircuit t
  (equalityConstrainableColumns lc t)
  (lookupArguments lc t)
  (equalityConstraints lc t)
  where
    t = logicCircuitToTraceType lc

-- Each lookup argument in the logic circuit results in a
-- step type, and a lookup argument, gated to the step type
-- corresponding, which is the same lookup argument with the
-- column indices substituted for input column
-- indices in the trace type.
lookupArguments
  :: LogicCircuit
  -> TraceType
  -> LookupArguments
lookupArguments = todo

equalityConstrainableColumns
  :: LogicCircuit
  -> TraceType
  -> EqualityConstrainableColumns
equalityConstrainableColumns = todo

equalityConstraints
  :: LogicCircuit
  -> TraceType
  -> EqualityConstraints
equalityConstraints = todo

todo :: a
todo = todo
