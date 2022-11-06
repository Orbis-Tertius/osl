module Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit) where

import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import Halo2.Types.EqualityConstraints (EqualityConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Trace.Types (TraceType)

traceTypeToArithmeticCircuit
  :: TraceType
  -> EqualityConstrainableColumns
  -> LookupArguments
  -> EqualityConstraints
  -> ArithmeticCircuit
traceTypeToArithmeticCircuit = todo

todo :: a
todo = todo
