{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}

module Trace.FromLogicCircuit
  ( logicCircuitToTraceType
  ) where


import Halo2.Prelude
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.RowCount (RowCount (RowCount))
import Stark.Types.Scalar (Scalar)
import Trace.Types (TraceType (TraceType), NumberOfCases (NumberOfCases), StepTypeId, StepType, SubexpressionId, SubexpressionLink, ResultExpressionId, CaseNumberColumnIndex, StepTypeColumnIndex, InputColumnIndex, OutputColumnIndex, StepIndicatorColumnIndex)


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
  caseNumColIdx
  stepTypeColIdx
  stepIndColIdx
  inputColIdxs
  outputColIdxs
  (NumberOfCases (rowCount ^. #getRowCount))
  (rowCount * RowCount (maxStepsPerCase colTypes' stepTypes subexprs links resultId))
  where
    rowCount = c ^. #rowCount

    (colTypes', stepTypes, subexprs, links, resultId, caseNumColIdx, stepTypeColIdx, stepIndColIdx, inputColIdxs, outputColIdxs) =
      todo c


data Mapping =
  Mapping
  { caseNumber :: CaseNumberColumnIndex,
    stepType :: StepTypeColumnIndex,
    stepIndicator :: StepIndicatorColumnIndex,
    inputs :: [InputColumnIndex],
    output :: OutputColumnIndex,
    byteDecomposition :: ByteDecompositionMapping,
    truthTable :: TruthTableColumnIndices
  }
  deriving Generic

data ByteDecompositionMapping =
  ByteDecompositionMapping
  { sign :: SignColumnIndex,
    bytes :: [(ByteColumnIndex, TruthValueColumnIndex)] -- most significant first
  }
  deriving Generic

newtype TruthValueColumnIndex = TruthValueColumnIndex
  {unTruthValueColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype SignColumnIndex = SignColumnIndex {unSignColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype ByteColumnIndex = ByteColumnIndex {unByteColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype ByteRangeColumnIndex = ByteRangeColumnIndex
  {unByteRangeColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype ZeroIndicatorColumnIndex = ZeroIndicatorColumnIndex
  {unZeroIndicatorColumnIndex :: ColumnIndex}
  deriving (Generic)

data TruthTableColumnIndices = TruthTableColumnIndices
  { byteRangeColumnIndex :: ByteRangeColumnIndex,
    zeroIndicatorColumnIndex :: ZeroIndicatorColumnIndex
  }
  deriving (Generic)

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
