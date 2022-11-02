{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout
  ( OutputMapping (OutputMapping),
    ArgMapping (ArgMapping),
    NameMapping (NameMapping),
    TermMapping (TermMapping),
    OneVectorIndex (OneVectorIndex),
    ZeroVectorIndex (ZeroVectorIndex),
    LastRowIndicatorColumnIndex (LastRowIndicatorColumnIndex),
    FixedColumns (FixedColumns),
    DummyRowAdviceColumn (DummyRowAdviceColumn),
    SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout),
  )
where

import Data.Map (Map)
import GHC.Generics (Generic)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Semicircuit.Types.Sigma11 (Name, Term)

newtype OutputMapping = OutputMapping {unOutputMapping :: ColumnIndex}
  deriving stock Generic
  deriving newtype Show

newtype ArgMapping = ArgMapping {unArgMapping :: ColumnIndex}
  deriving stock Generic
  deriving newtype Show

data NameMapping = NameMapping
  { outputMapping :: OutputMapping,
    argMappings :: [ArgMapping]
  }
  deriving (Generic, Show)

newtype TermMapping = TermMapping {unTermMapping :: ColumnIndex}
  deriving stock Generic
  deriving newtype Show

newtype ZeroVectorIndex = ZeroVectorIndex {unZeroVectorIndex :: ColumnIndex}
  deriving stock Generic
  deriving newtype Show

newtype OneVectorIndex = OneVectorIndex {unOneVectorIndex :: ColumnIndex}
  deriving stock Generic
  deriving newtype Show

newtype LastRowIndicatorColumnIndex = LastRowIndicatorColumnIndex
  {unLastRowIndicatorColumnIndex :: ColumnIndex}
  deriving stock Generic
  deriving newtype Show

data FixedColumns = FixedColumns
  { zeroVector :: ZeroVectorIndex,
    oneVector :: OneVectorIndex,
    lastRowIndicator :: LastRowIndicatorColumnIndex
  }
  deriving stock (Generic, Show)

newtype DummyRowAdviceColumn = DummyRowAdviceColumn
  {unDummyRowAdviceColumn :: ColumnIndex}
  deriving Generic
  deriving newtype Show

data SemicircuitToLogicCircuitColumnLayout = SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping,
    termMappings :: Map Term TermMapping,
    fixedColumns :: FixedColumns,
    dummyRowAdviceColumn :: DummyRowAdviceColumn
  }
  deriving stock (Generic, Show)
