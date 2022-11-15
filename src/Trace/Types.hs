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
  , StepIndicatorColumnIndex (StepIndicatorColumnIndex)
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


-- All step types for a trace type should have the same number of inputs. When
-- a step type has fewer ``real'' inputs than the total number of inputs,
-- the extra inputs in its links table entries should be wired to a special
-- subexpression id called void. The step type of void has no constraints.
-- The links table entry outputting void has all its inputs set to void.
-- Void's value can legally be set to anything. Each trace type features void.
data StepType =
  StepType
  { gateConstraints :: PolynomialConstraints
  , lookupArguments :: LookupArguments
  , fixedValues :: FixedValues
  }
  deriving Generic


newtype StepTypeId = StepTypeId { unStepTypeId :: Scalar }
  deriving (Generic, Eq)


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


newtype StepIndicatorColumnIndex =
  StepIndicatorColumnIndex { unStepIndicatorColumnIndex :: ColumnIndex }
  deriving Generic


newtype NumberOfCases =
  NumberOfCases { unNumberOfCases :: Scalar }
  deriving Generic


data TraceType =
  TraceType
  { columnTypes :: ColumnTypes
  , stepTypes :: Map StepTypeId StepType
  , subexpressions :: Set SubexpressionId
  , links :: Set SubexpressionLink
  , result :: ResultExpressionId
  , stepTypeColumnIndex :: StepTypeColumnIndex
  , stepIndicatorColumnIndex :: StepIndicatorColumnIndex
  , inputColumnIndices :: [InputColumnIndex]
  , outputColumnIndices :: [OutputColumnIndex]
  , numCases :: NumberOfCases
  , rowCount :: RowCount
  }
  deriving Generic
