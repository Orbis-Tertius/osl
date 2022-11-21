{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}

module Trace.FromLogicCircuit
  ( logicCircuitToTraceType
  , getMapping
  ) where


import Control.Monad (replicateM)
import Control.Monad.Trans.State (State, evalState, get, put)
import qualified Data.Map as Map
import Halo2.Prelude
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.RowCount (RowCount (RowCount))
import Stark.Types.Scalar (Scalar)
import OSL.Types.Arity (Arity)
import Trace.Types (TraceType (TraceType), NumberOfCases (NumberOfCases), StepTypeId, StepType, SubexpressionId, SubexpressionLink, ResultExpressionId, CaseNumberColumnIndex (..), StepTypeColumnIndex (..), InputColumnIndex (..), OutputColumnIndex (..), StepIndicatorColumnIndex (..))


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
  (mapping ^. #caseNumber)
  (mapping ^. #stepType)
  (mapping ^. #stepIndicator)
  (mapping ^. #inputs)
  (mapping ^. #output)
  (NumberOfCases (rowCount ^. #getRowCount))
  (rowCount * RowCount (maxStepsPerCase colTypes' stepTypes subexprs links resultId))
  where
    rowCount = c ^. #rowCount

    mapping = getMapping c

    colTypes' = getColumnTypes c mapping

    stepTypes = getStepTypes c mapping

    (subexprs, links, resultId) = getSubexpressions c mapping stepTypes

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

newtype S = S { unS :: ColumnIndex }

getStepArity :: LogicCircuit -> Arity
getStepArity = todo

getByteDecompositionLength :: LogicCircuit -> Int
getByteDecompositionLength = todo

getMapping :: LogicCircuit -> Mapping
getMapping c =
  evalState go (S (ColumnIndex (length (Map.keys (c ^. #columnTypes . #getColumnTypes)))))
  where
    next :: State S ColumnIndex
    next = do
      i <- unS <$> get
      put (S (i+1))
      pure i

    go :: State S Mapping
    go =
      Mapping
        <$> (CaseNumberColumnIndex <$> next)
        <*> (StepTypeColumnIndex <$> next)
        <*> (StepIndicatorColumnIndex <$> next)
        <*> replicateM (getStepArity c ^. #unArity)
            (InputColumnIndex <$> next)
        <*> (OutputColumnIndex <$> next)
        <*> (ByteDecompositionMapping
              <$> (SignColumnIndex <$> next)
              <*> replicateM
                  (getByteDecompositionLength c)
                  ((,) <$> (ByteColumnIndex <$> next)
                       <*> (TruthValueColumnIndex <$> next)))
        <*> (TruthTableColumnIndices
              <$> (ByteRangeColumnIndex <$> next)
              <*> (ZeroIndicatorColumnIndex <$> next))

getColumnTypes :: LogicCircuit -> Mapping -> ColumnTypes
getColumnTypes = todo

getStepTypes
  :: LogicCircuit
  -> Mapping
  -> Map StepTypeId StepType
getStepTypes = todo

getSubexpressions
  :: LogicCircuit
  -> Mapping
  -> Map StepTypeId StepType
  -> (Set SubexpressionId,
      Set SubexpressionLink,
      ResultExpressionId)
getSubexpressions = todo

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
