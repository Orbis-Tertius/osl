{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Halo2.Types.CircuitMetrics
  ( CircuitMetrics (CircuitMetrics),
    RowCount (RowCount),
    ColumnClass (Advice, Instance, Fixed, All, EqualityConstrainable),
    ColumnCounts (ColumnCounts),
    ColumnCount (ColumnCount),
    PolynomialDegreeBound (PolynomialDegreeBound),
    GateConstraintCount (GateConstraintCount),
    LookupArgumentCount (LookupArgumentCount),
    LookupTableSize (LookupTableSize),
  )
where

import Data.Kind (Type)
import GHC.Generics (Generic)
import Halo2.Types.PolynomialDegreeBound (PolynomialDegreeBound (PolynomialDegreeBound))
import Halo2.Types.RowCount (RowCount (RowCount))

data CircuitMetrics = CircuitMetrics
  { rowCount :: RowCount,
    columnCounts :: ColumnCounts,
    polyDegreeBound :: PolynomialDegreeBound,
    gateConstraintCount :: GateConstraintCount,
    lookupArgumentCount :: LookupArgumentCount,
    lookupTableSize :: LookupTableSize
  }
  deriving stock (Generic, Show)

data ColumnClass
  = Advice
  | Instance
  | Fixed
  | All
  | EqualityConstrainable

data ColumnCounts = ColumnCounts
  { advice :: ColumnCount Advice,
    instances :: ColumnCount Instance,
    fixed :: ColumnCount Fixed,
    all :: ColumnCount All,
    eqc :: ColumnCount EqualityConstrainable
  }
  deriving stock (Generic, Show)

type ColumnCount :: ColumnClass -> Type
newtype ColumnCount a = ColumnCount {unColumnCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype GateConstraintCount = GateConstraintCount {unGateConstraintCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype LookupArgumentCount = LookupArgumentCount {unLookupArgumentCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype LookupTableSize = LookupTableSize {unLookupTableSize :: Int}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Num, Show)
