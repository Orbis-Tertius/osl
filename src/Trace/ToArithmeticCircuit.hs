module Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit) where

import Halo2.AIR (toCircuit)
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import Halo2.Types.EqualityConstraints (EqualityConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Trace.ToArithmeticAIR (traceTypeToArithmeticAIR)
import Trace.Types (TraceType)

traceTypeToArithmeticCircuit
  :: TraceType
  -> EqualityConstrainableColumns
  -> LookupArguments
  -> EqualityConstraints
  -> ArithmeticCircuit
traceTypeToArithmeticCircuit traceType eqcs lookups eqs =
  toCircuit
  (traceTypeToArithmeticAIR traceType)
  eqcs
  (lookups <> traceTypeLookupArguments traceType)
  eqs

-- Trace type lookup arguments entail that for each step
-- of each case, for each input to the step, there is a step
-- of the same case which outputs that input.
traceTypeLookupArguments
  :: TraceType
  -> LookupArguments
traceTypeLookupArguments = todo

todo :: a
todo = todo
