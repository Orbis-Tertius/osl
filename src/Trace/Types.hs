{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}


module Trace.Types
  ( InputColumnIndex (InputColumnIndex)
  , OutputColumnIndex (OutputColumnIndex)
  , StepType (StepType)
  , StepTypeId (StepTypeId)
  , SubexpressionId (SubexpressionId)
  , SubexpressionLink (SubexpressionLink)
  , TraceType (TraceType)
  ) where


import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.FixedValues (FixedValues)
import Semicircuit.Types.Sigma11 (Name)
import Semicircuit.Types.PNFFormula (Quantifiers)
import Semicircuit.Types.NameMapping (NameMapping)


newtype InputColumnIndex =
  InputColumnIndex { unInputColumnIndex :: ColumnIndex }
  deriving Generic


newtype OutputColumnIndex =
  OutputColumnIndex { unOutputColumnIndex :: ColumnIndex }
  deriving Generic


data StepType =
  StepType
  { inputs :: [InputColumnIndex]
  , outputs :: [OutputColumnIndex]
  , gateConstraints :: [Polynomial]
  , lookupArguments :: LookupArguments
  , fixedValues :: FixedValues
  }
  deriving Generic


newtype StepTypeId = StepTypeId { unStepTypeId :: Int }
  deriving Generic


data SubexpressionId = SubexpressionId { unSubexpressionId :: Int }
  deriving Generic


data SubexpressionLink =
  SubexpressionLink
  { inputs :: [SubexpressionId]
  , outputs :: [SubexpressionId]
  , stepType :: StepTypeId
  }
  deriving Generic


newtype ResultExpressionId =
  ResultExpressionId { unResultExpressionId :: SubexpressionId }
  deriving Generic


data TraceType =
  TraceType
  { stepTypes :: Map StepTypeId StepType
  , subexpressions :: Set SubexpressionId
  , links :: Set SubexpressionLink
  , result :: ResultExpressionId
  , quantifiers :: Quantifiers
  , nameMappings :: Map Name NameMapping
  }
  deriving Generic
