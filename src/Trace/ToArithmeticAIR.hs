module Trace.ToArithmeticAIR (traceTypeToArithmeticAIR) where

import Halo2.Types.AIR (ArithmeticAIR)
import Trace.Types (TraceType)

-- Trace type arithmetic AIRs have the columnar structure
-- of the trace type, with additional fixed columns for:
--  * the table of links, and
--  * the table {(i,1) | i < numCases}.
--
-- Trace type arithmetic AIR gate constraints entail that
-- for each step of each case, the gate constraints of
-- its step type are satisfied.
traceTypeToArithmeticAIR :: TraceType -> ArithmeticAIR
traceTypeToArithmeticAIR = todo

todo :: a
todo = todo
