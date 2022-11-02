{-# LANGUAGE DeriveGeneric #-}

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
  deriving (Generic, Show)

newtype ArgMapping = ArgMapping {unArgMapping :: ColumnIndex}
  deriving (Generic, Show)

data NameMapping = NameMapping
  { outputMapping :: OutputMapping,
    argMappings :: [ArgMapping]
  }
  deriving (Generic, Show)

newtype TermMapping = TermMapping {unTermMapping :: ColumnIndex}
  deriving (Generic)

newtype ZeroVectorIndex = ZeroVectorIndex {unZeroVectorIndex :: ColumnIndex}
  deriving (Generic)

newtype OneVectorIndex = OneVectorIndex {unOneVectorIndex :: ColumnIndex}
  deriving (Generic)

newtype LastRowIndicatorColumnIndex = LastRowIndicatorColumnIndex
  {unLastRowIndicatorColumnIndex :: ColumnIndex}
  deriving (Generic)

data FixedColumns = FixedColumns
  { zeroVector :: ZeroVectorIndex,
    oneVector :: OneVectorIndex,
    lastRowIndicator :: LastRowIndicatorColumnIndex
  }
  deriving (Generic)

newtype DummyRowAdviceColumn = DummyRowAdviceColumn
  {unDummyRowAdviceColumn :: ColumnIndex}
  deriving (Generic)

data SemicircuitToLogicCircuitColumnLayout = SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping,
    termMappings :: Map Term TermMapping,
    fixedColumns :: FixedColumns,
    dummyRowAdviceColumn :: DummyRowAdviceColumn
  }
  deriving (Generic)
