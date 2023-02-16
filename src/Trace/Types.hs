{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}

module Trace.Types
  ( InputColumnIndex (InputColumnIndex),
    OutputColumnIndex (OutputColumnIndex),
    StepType (StepType),
    StepTypeId (StepTypeId),
    SubexpressionId (SubexpressionId),
    InputSubexpressionId (InputSubexpressionId),
    OutputSubexpressionId (OutputSubexpressionId),
    SubexpressionLink (SubexpressionLink),
    ResultExpressionId (ResultExpressionId),
    StepIndicatorColumnIndex (StepIndicatorColumnIndex),
    CaseNumberColumnIndex (CaseNumberColumnIndex),
    NumberOfCases (NumberOfCases),
    Case (Case),
    StepTypeIdSelectionVector (StepTypeIdSelectionVector),
    TraceType (TraceType),
    Trace (Trace),
    SubexpressionTrace (SubexpressionTrace),
    Statement (Statement),
    Witness (Witness),
  )
where

import qualified Algebra.Additive as Group
import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import Halo2.Types.EqualityConstraints (EqualityConstraints)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.Label (Label)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints)
import Halo2.Types.RowCount (RowCount)
import Stark.Types.Scalar (Scalar)

newtype InputColumnIndex = InputColumnIndex {unInputColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

newtype OutputColumnIndex = OutputColumnIndex {unOutputColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

-- All step types for a trace type should have the same number of inputs. When
-- a step type has fewer ``real'' inputs than the total number of inputs,
-- the extra inputs in its links table entries should be wired to a special
-- subexpression id called void. The step type of void has no constraints.
-- The links table entry outputting void has all its inputs set to void.
-- Void's value can legally be set to anything. Each trace type features void.
data StepType = StepType
  { label :: Label,
    gateConstraints :: PolynomialConstraints,
    lookupArguments :: LookupArguments Polynomial,
    fixedValues :: FixedValues Case
  }
  deriving (Generic, Show)

instance Semigroup StepType where
  (StepType l a b c) <> (StepType _ d e f) =
    StepType l (a <> d) (b <> e) (c <> f)

instance Monoid StepType where
  mempty = StepType mempty mempty mempty mempty

newtype StepTypeId = StepTypeId {unStepTypeId :: Scalar}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Num, Show)

newtype SubexpressionId = SubexpressionId {unSubexpressionId :: Scalar}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Num, Show)

newtype InputSubexpressionId = InputSubexpressionId {unInputSubexpressionId :: SubexpressionId}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show)

newtype OutputSubexpressionId = OutputSubexpressionId {unOutputSubexpressionId :: SubexpressionId}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show)

data SubexpressionLink = SubexpressionLink
  { stepType :: StepTypeId,
    inputs :: [InputSubexpressionId],
    output :: OutputSubexpressionId
  }
  deriving (Eq, Ord, Generic, Show)

newtype ResultExpressionId = ResultExpressionId {unResultExpressionId :: SubexpressionId}
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord)

newtype CaseNumberColumnIndex = CaseNumberColumnIndex {unCaseNumberColumnIndex :: ColumnIndex}
  deriving stock (Generic)
  deriving newtype (Show)

newtype StepIndicatorColumnIndex = StepIndicatorColumnIndex {unStepIndicatorColumnIndex :: ColumnIndex}
  deriving stock (Generic)
  deriving newtype (Show)

newtype NumberOfCases = NumberOfCases {unNumberOfCases :: Scalar}
  deriving stock (Generic)
  deriving newtype (Show)

-- We represent step type ids as selection vectors, i.e. vectors
-- of bits containing exactly one 1 bit.
newtype StepTypeIdSelectionVector = StepTypeIdSelectionVector
  {unStepTypeIdSelectionVector :: Map StepTypeId ColumnIndex}
  deriving (Generic, Show)

data TraceType = TraceType
  { -- All column types, both those inherited from the logic circuit and those
    -- newly added in the trace type
    columnTypes :: ColumnTypes,
    equalityConstrainableColumns :: EqualityConstrainableColumns,
    equalityConstraints :: EqualityConstraints,
    -- Fixed values inherited from the logic circuit
    fixedValues :: FixedValues Case,
    stepTypes :: Map StepTypeId StepType,
    subexpressions :: Set SubexpressionId,
    links :: Map (StepTypeId, OutputSubexpressionId) [InputSubexpressionId],
    results :: Set ResultExpressionId,
    caseNumberColumnIndex :: CaseNumberColumnIndex,
    stepTypeIdColumnIndices :: StepTypeIdSelectionVector,
    -- this column contains 1 if this row contains a step, and 0 otherwise
    stepIndicatorColumnIndex :: StepIndicatorColumnIndex,
    inputColumnIndices :: [InputColumnIndex],
    outputColumnIndex :: OutputColumnIndex,
    numCases :: NumberOfCases,
    rowCount :: RowCount
  }
  deriving (Generic, Show)

newtype Case = Case {unCase :: Scalar}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show, Group.C)

newtype Statement = Statement {unStatement :: Map (Case, ColumnIndex) Scalar}
  deriving (Generic, Show)

newtype Witness = Witness {unWitness :: Map (Case, ColumnIndex) Scalar}
  deriving (Generic, Show)

data Trace = Trace
  { statement :: Statement,
    witness :: Witness,
    subexpressions :: Map Case (Map SubexpressionId SubexpressionTrace)
  }
  deriving (Generic, Show)

data SubexpressionTrace = SubexpressionTrace
  { value :: Scalar, -- output value
    stepType :: StepTypeId,
    adviceValues :: Map ColumnIndex Scalar
  }
  deriving (Generic, Show)
