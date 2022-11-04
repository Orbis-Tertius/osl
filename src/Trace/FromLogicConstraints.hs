{-# LANGUAGE OverloadedLabels #-}

module Trace.FromLogicConstraints
  ( logicConstraintsToTraceType
  ) where


import Halo2.Prelude
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.RowCount (RowCount (RowCount))
import Trace.Types (TraceType (TraceType), NumberOfCases (NumberOfCases), StepTypeId, StepType, SubexpressionId, SubexpressionLink, ResultExpressionId)


logicConstraintsToTraceType
  :: ColumnTypes
  -> RowCount
  -> LogicConstraints
  -> TraceType
logicConstraintsToTraceType colTypes rowCount constraints =
  TraceType
  colTypes'
  stepTypes
  subexprs
  links
  resultId
  (NumberOfCases (rowCount ^. #getRowCount))
  (rowCount * RowCount (maxStepsPerCase colTypes' stepTypes subexprs links resultId))
  where
    (colTypes', stepTypes, subexprs, links, resultId) =
      todo colTypes constraints


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
