{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Semicircuit.Types.NameMapping
  ( OutputMapping (OutputMapping),
    ArgMapping (ArgMapping),
    NameMapping (NameMapping),
  )
where

import GHC.Generics (Generic)
import Halo2.Types.ColumnIndex (ColumnIndex)

newtype OutputMapping = OutputMapping {unOutputMapping :: ColumnIndex}
  deriving stock (Generic)
  deriving newtype (Show)

newtype ArgMapping = ArgMapping {unArgMapping :: ColumnIndex}
  deriving stock (Generic)
  deriving newtype (Show)

data NameMapping = NameMapping
  { outputMapping :: OutputMapping,
    argMappings :: [ArgMapping]
  }
  deriving (Generic, Show)
