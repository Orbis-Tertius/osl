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

-- Trace type lookup arguments entail that:
--  * For each step of each case, for each input to the step,
--    there is a step of the same case which outputs that input.
--  * For each step of each case, its vector of input and
--    output subexpression ids is in the links table.
--  * For each case, there is a step of the result
--    subexpression id and its output is 1.
-- They also include the lookup arguments for each step type.
traceTypeLookupArguments
  :: TraceType
  -> LookupArguments
traceTypeLookupArguments = todo

todo :: a
todo = todo
