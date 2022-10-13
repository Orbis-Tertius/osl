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
import Semicircuit.Types.Sigma11 (Name)

newtype OutputMapping =
  HeadMapping { unHeadMapping :: ColumnIndex }

newtype ArgMapping =
  ArgMapping { unArgMapping :: ColumnIndex }

data NameMapping =
  NameMapping
  { outputMapping :: OutputMapping
  , argMappings :: [ArgMapping]
  }
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

data SemicircuitToLogicCircuitColumnLayout =
  SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping,
    fixedColumns :: FixedColumns
  }
  deriving Generic
