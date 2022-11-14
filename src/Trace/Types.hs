{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}


module Trace.Types
  ( InputColumnIndex (InputColumnIndex)
  , OutputColumnIndex (OutputColumnIndex)
  , StepType (StepType)
  , StepTypeId (StepTypeId)
  , SubexpressionId (SubexpressionId)
  , InputSubexpressionId (InputSubexpressionId)
  , OutputSubexpressionId (OutputSubexpressionId)
  , SubexpressionLink (SubexpressionLink)
  , ResultExpressionId (ResultExpressionId)
  , NumberOfCases (NumberOfCases)
  , TraceType (TraceType)
  ) where


import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.RowCount (RowCount)


newtype InputColumnIndex =
  InputColumnIndex { unInputColumnIndex :: ColumnIndex }
  deriving Generic


newtype OutputColumnIndex =
  OutputColumnIndex { unOutputColumnIndex :: ColumnIndex }
  deriving Generic


data StepType =
  StepType
  { inputs :: [InputColumnIndex]
  , output :: OutputColumnIndex
  , gateConstraints :: [Polynomial]
  , lookupArguments :: LookupArguments
  , fixedValues :: FixedValues
  }
  deriving Generic


newtype StepTypeId = StepTypeId { unStepTypeId :: Int }
  deriving Generic


newtype SubexpressionId = SubexpressionId { unSubexpressionId :: Int }
  deriving Generic

newtype InputSubexpressionId = InputSubexpressionId { unInputSubexpressionId :: Int }
  deriving Generic

newtype OutputSubexpressionId = OutputSubexpressionId { unOutputSubexpressionId :: Int }
  deriving Generic


data SubexpressionLink =
  SubexpressionLink
  { stepType :: StepTypeId
  , inputs :: [InputSubexpressionId]
  , output :: OutputSubexpressionId
  }
  deriving Generic


newtype ResultExpressionId =
  ResultExpressionId { unResultExpressionId :: SubexpressionId }
  deriving Generic


newtype NumberOfCases =
  NumberOfCases { unNumberOfCases :: Int }
  deriving Generic


data TraceType =
  TraceType
  { columnTypes :: ColumnTypes
  , stepTypes :: Map StepTypeId StepType
  , subexpressions :: Set SubexpressionId
  , links :: Set SubexpressionLink
  , result :: ResultExpressionId
  , numCases :: NumberOfCases
  , rowCount :: RowCount
  }
  deriving Generic
