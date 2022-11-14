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
  , StepTypeColumnIndex (StepTypeColumnIndex)
  , NumberOfCases (NumberOfCases)
  , TraceType (TraceType)
  ) where


import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.RowCount (RowCount)
import Stark.Types.Scalar (Scalar)


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
  , gateConstraints :: PolynomialConstraints
  , lookupArguments :: LookupArguments
  , fixedValues :: FixedValues
  }
  deriving Generic


newtype StepTypeId = StepTypeId { unStepTypeId :: Scalar }
  deriving Generic


newtype SubexpressionId = SubexpressionId { unSubexpressionId :: Scalar }
  deriving Generic

newtype InputSubexpressionId = InputSubexpressionId { unInputSubexpressionId :: SubexpressionId }
  deriving Generic

newtype OutputSubexpressionId = OutputSubexpressionId { unOutputSubexpressionId :: SubexpressionId }
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


newtype StepTypeColumnIndex =
  StepTypeColumnIndex { unStepTypeColumnIndex :: ColumnIndex }
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
  , stepTypeColumnIndex :: StepTypeColumnIndex
  , inputColumnIndices :: [InputColumnIndex]
  , outputColumnIndices :: [OutputColumnIndex]
  , numCases :: NumberOfCases
  , rowCount :: RowCount
  }
  deriving Generic
