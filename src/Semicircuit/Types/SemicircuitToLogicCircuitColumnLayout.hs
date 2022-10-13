{-# LANGUAGE DeriveGeneric #-}

module Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout
  ( OutputMapping (..)
  , ArgMapping (..)
  , NameMapping (NameMapping)
  , OneVectorIndex (..)
  , ZeroVectorIndex (..)
  , LastRowIndicatorColumnIndex (..)
  , FixedColumns (..)
  , SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout)
  ) where

import Data.Map (Map)
import GHC.Generics (Generic)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
import Semicircuit.Types.Sigma11 (Name, Term)

newtype OutputMapping =
  HeadMapping { unOutputMapping :: ColumnIndex }
  deriving Generic

newtype ArgMapping =
  ArgMapping { unArgMapping :: ColumnIndex }
  deriving Generic

data NameMapping =
  NameMapping
  { outputMapping :: OutputMapping
  , argMappings :: [ArgMapping]
  }
  deriving Generic

data TermMapping =
  TermMapping { unTermMapping :: Name }
  deriving Generic

newtype ZeroVectorIndex =
  ZeroVectorIndex { unZeroVectorIndex :: ColumnIndex }
  deriving Generic

newtype OneVectorIndex =
  OneVectorIndex { unOneVectorIndex :: ColumnIndex }

newtype LastRowIndicatorColumnIndex =
  LastRowIndicatorColumnIndex
  { unLastRowIndicatorColumnIndex :: ColumnIndex }

data FixedColumns =
  FixedColumns
  { zeroVector :: ZeroVectorIndex
  , oneVector :: OneVectorIndex
  , lastRowIndicator :: LastRowIndicatorColumnIndex
  }
  deriving Generic

newtype DummyRowAdviceColumn =
  DummyRowAdviceColumn
  { unDummyRowAdviceColumn :: ColumnIndex }
  deriving Generic

data SemicircuitToLogicCircuitColumnLayout =
  SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping,
    termMappings :: Map Term TermMapping,
    fixedColumns :: FixedColumns,
    dummyRowAdviceColumn :: DummyRowAdviceColumn
  }
  deriving Generic
