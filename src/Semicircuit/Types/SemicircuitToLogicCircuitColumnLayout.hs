{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout
  ( OutputMapping (OutputMapping),
    ArgMapping (ArgMapping),
    NameMapping (NameMapping),
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
import Semicircuit.Types.NameMapping (ArgMapping (ArgMapping), NameMapping (NameMapping), OutputMapping (OutputMapping))
import Semicircuit.Types.Sigma11 (Name)

newtype LastRowIndicatorColumnIndex = LastRowIndicatorColumnIndex
  {unLastRowIndicatorColumnIndex :: ColumnIndex}
  deriving stock (Generic)
  deriving newtype (Show)

newtype FixedColumns = FixedColumns
  { lastRowIndicator :: LastRowIndicatorColumnIndex
  }
  deriving stock (Generic, Show)

newtype DummyRowAdviceColumn = DummyRowAdviceColumn
  {unDummyRowAdviceColumn :: ColumnIndex}
  deriving (Generic)
  deriving newtype (Show)

data SemicircuitToLogicCircuitColumnLayout = SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping,
    fixedColumns :: FixedColumns,
    dummyRowAdviceColumn :: DummyRowAdviceColumn
  }
  deriving stock (Generic, Show)
