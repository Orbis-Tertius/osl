{-# LANGUAGE OverloadedLabels #-}

module Trace.FromLogicAIR
  ( logicAIRToTraceType
  ) where


import Halo2.Prelude
import Halo2.Types.AIR (LogicAIR)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.RowCount (RowCount (RowCount))
import Trace.Types (TraceType (TraceType), NumberOfCases (NumberOfCases), StepTypeId, StepType, SubexpressionId, SubexpressionLink, ResultExpressionId)


logicAIRToTraceType
  :: LogicAIR
  -> TraceType
logicAIRToTraceType air =
  TraceType
  colTypes'
  stepTypes
  subexprs
  links
  resultId
  stepTypeColIdx
  (NumberOfCases (rowCount ^. #getRowCount))
  (rowCount * RowCount (maxStepsPerCase colTypes' stepTypes subexprs links resultId))
  where
    rowCount = air ^. #rowCount

    (colTypes', stepTypes, subexprs, links, resultId, stepTypeColIdx) =
      todo air


maxStepsPerCase
  :: ColumnTypes
  -> Map StepTypeId StepType
  -> Set SubexpressionId
  -> Set SubexpressionLink
  -> ResultExpressionId
  -> Int
maxStepsPerCase = todo


todo :: a
todo = todo
