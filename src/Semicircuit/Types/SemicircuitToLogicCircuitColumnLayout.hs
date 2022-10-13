{-# LANGUAGE DeriveGeneric #-}

module Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout
  ( OutputMapping (..)
  , ArgMapping (..)
  , NameMapping (NameMapping)
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

data SemicircuitToLogicCircuitColumnLayout =
  SemicircuitToLogicCircuitColumnLayout
  { columnTypes :: ColumnTypes,
    nameMappings :: Map Name NameMapping
  }
  deriving Generic
