{-# LANGUAGE DeriveGeneric #-}

module Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout
  ( OutputMapping (OutputMapping),
    ArgMapping (ArgMapping),
    NameMapping (NameMapping),
    TermMapping (TermMapping),
    OneVectorIndex (OneVectorIndex),
    ZeroVectorIndex (ZeroVectorIndex),
    LastRowIndicatorColumnIndex (LastRowIndicatorColumnIndex),
    FixedFunctionTable (FixedFunctionTable),
    FixedSetTable (FixedSetTable),
    FixedColumns (FixedColumns),
    SetMapping (SetMapping),
    DummyRowAdviceColumn (DummyRowAdviceColumn),
    SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout),
  )
where

import Data.Map (Map)
import GHC.Generics (Generic)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import OSL.Types.Sigma11 (PredicateName)
import Semicircuit.Types.Sigma11 (Name, Term)

newtype OutputMapping = OutputMapping {unOutputMapping :: ColumnIndex}
  deriving (Generic)

newtype ArgMapping = ArgMapping {unArgMapping :: ColumnIndex}
  deriving (Generic)

data NameMapping = NameMapping
  { outputMapping :: OutputMapping,
    argMappings :: [ArgMapping]
  }
  deriving (Generic)

newtype TermMapping = TermMapping {unTermMapping :: ColumnIndex}
  deriving (Generic)

newtype ZeroVectorIndex = ZeroVectorIndex {unZeroVectorIndex :: ColumnIndex}
  deriving (Generic)

newtype OneVectorIndex = OneVectorIndex {unOneVectorIndex :: ColumnIndex}
  deriving (Generic)

newtype LastRowIndicatorColumnIndex = LastRowIndicatorColumnIndex
  {unLastRowIndicatorColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype FixedFunctionTable = FixedFunctionTable
  { unFixedFunctionTable :: NameMapping }
  deriving (Generic)

newtype FixedSetTable = FixedSetTable
  { unFixedSetTable :: [ColumnIndex] }
  deriving Generic

data FixedColumns = FixedColumns
  { zeroVector :: ZeroVectorIndex,
    oneVector :: OneVectorIndex,
    lastRowIndicator :: LastRowIndicatorColumnIndex,
    fixedFunctionTables :: Map Name FixedFunctionTable,
    fixedSetTables :: Map PredicateName FixedSetTable
  }
  deriving (Generic)

newtype SetMapping = SetMapping { unSetMapping :: NameMapping }
  deriving (Generic)

newtype DummyRowAdviceColumn = DummyRowAdviceColumn
  {unDummyRowAdviceColumn :: ColumnIndex}
  deriving (Generic)

data SemicircuitToLogicCircuitColumnLayout = SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping,
    termMappings :: Map Term TermMapping,
    setMappings :: Map PredicateName SetMapping,
    fixedColumns :: FixedColumns,
    dummyRowAdviceColumn :: DummyRowAdviceColumn
  }
  deriving (Generic)
