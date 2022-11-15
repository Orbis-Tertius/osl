{-# LANGUAGE OverloadedLabels #-}

module Trace.FromLogicCircuit
  ( logicCircuitToTraceType
  ) where


import Halo2.Prelude
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.RowCount (RowCount (RowCount))
import Stark.Types.Scalar (Scalar)
import Trace.Types (TraceType (TraceType), NumberOfCases (NumberOfCases), StepTypeId, StepType, SubexpressionId, SubexpressionLink, ResultExpressionId)


logicCircuitToTraceType
  :: LogicCircuit
  -> TraceType
logicCircuitToTraceType c =
  TraceType
  colTypes'
  stepTypes
  subexprs
  links
  resultId
  stepTypeColIdx
  stepIndColIdx
  inputColIdxs
  outputColIdxs
  (NumberOfCases (rowCount ^. #getRowCount))
  (rowCount * RowCount (maxStepsPerCase colTypes' stepTypes subexprs links resultId))
  where
    rowCount = c ^. #rowCount

    (colTypes', stepTypes, subexprs, links, resultId, stepTypeColIdx, stepIndColIdx, inputColIdxs, outputColIdxs) =
      todo c


maxStepsPerCase
  :: ColumnTypes
  -> Map StepTypeId StepType
  -> Set SubexpressionId
  -> Set SubexpressionLink
  -> ResultExpressionId
  -> Scalar
maxStepsPerCase = todo


todo :: a
todo = todo
