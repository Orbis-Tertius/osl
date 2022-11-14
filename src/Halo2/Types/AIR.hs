{-# LANGUAGE DeriveGeneric #-}

module Halo2.Types.AIR
  ( AIR (AIR)
  , ArithmeticAIR
  , LogicAIR
  ) where

import Halo2.Prelude
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints)
import Halo2.Types.RowCount (RowCount)

-- An AIR (Algebraic Intermediate Representation) is a circuit with
-- only gate constraints (no equality constraints or lookup arguments).
data AIR a = AIR
  { columnTypes :: ColumnTypes,
    gateConstraints :: a,
    rowCount :: RowCount,
    fixedValues :: FixedValues
  }
  deriving (Eq, Ord, Show, Generic)

type ArithmeticAIR = AIR PolynomialConstraints

type LogicAIR = AIR LogicConstraints
