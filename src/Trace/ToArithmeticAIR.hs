{-# LANGUAGE OverloadedLabels #-}

module Trace.ToArithmeticAIR (traceTypeToArithmeticAIR) where

import Halo2.Prelude
import Halo2.Types.AIR (AIR (AIR), ArithmeticAIR)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints)
import Trace.Types (TraceType, StepTypeId, InputSubexpressionId, OutputSubexpressionId)

-- Trace type arithmetic AIRs have the columnar structure
-- of the trace type, with additional fixed columns for:
--  * the table of links, and
--  * the table {(i,1) | i < numCases}.
--
-- Trace type arithmetic AIR gate constraints entail that
-- for each step of each case, the gate constraints of
-- its step type are satisfied.
traceTypeToArithmeticAIR :: TraceType -> ArithmeticAIR
traceTypeToArithmeticAIR t =
  AIR
  (columnTypes t)
  (gateConstraints t)
  (t ^. #rowCount)
  (additionalFixedValues t (fixedValueMappings t))

columnTypes :: TraceType -> ColumnTypes
columnTypes = todo

gateConstraints :: TraceType -> PolynomialConstraints
gateConstraints = todo

newtype Mapping a =
  Mapping { unMapping :: ColumnIndex }

data FixedValueMappings =
  FixedValueMappings
  { stepType :: Mapping StepTypeId
  , inputs :: [Mapping InputSubexpressionId]
  , output :: Mapping OutputSubexpressionId
  }

fixedValueMappings :: TraceType -> FixedValueMappings
fixedValueMappings = todo

additionalFixedValues
  :: TraceType
  -> FixedValueMappings
  -> FixedValues
additionalFixedValues = todo

todo :: a
todo = todo
