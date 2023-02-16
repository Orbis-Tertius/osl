module Trace.LogicToArithmetic
  ( logicCircuitToArithmeticCircuit,
  )
where

import Halo2.Types.BitsPerByte (BitsPerByte)
import Halo2.Types.Circuit (ArithmeticCircuit, LogicCircuit)
import Trace.FromLogicCircuit (getMapping, logicCircuitToTraceType)
import Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit)

logicCircuitToArithmeticCircuit ::
  BitsPerByte ->
  LogicCircuit ->
  ArithmeticCircuit
logicCircuitToArithmeticCircuit bitsPerByte lc =
  traceTypeToArithmeticCircuit
    (logicCircuitToTraceType bitsPerByte lc)
    (getMapping bitsPerByte lc)
