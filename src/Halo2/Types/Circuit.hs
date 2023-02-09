{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Circuit
  ( Circuit (Circuit),
    ArithmeticCircuit,
    LogicCircuit,
  )
where

import Halo2.Prelude
import Halo2.Types.ColumnTypes (ColumnTypes)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import Halo2.Types.EqualityConstraints (EqualityConstraints)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.LogicConstraint (Term)
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints)
import Halo2.Types.RowCount (RowCount)
import Halo2.Types.RowIndex (RowIndex, RowIndexType (Absolute))

data Circuit a b = Circuit
  { columnTypes :: ColumnTypes,
    equalityConstrainableColumns :: EqualityConstrainableColumns,
    gateConstraints :: a,
    lookupArguments :: LookupArguments b,
    rowCount :: RowCount,
    equalityConstraints :: EqualityConstraints,
    fixedValues :: FixedValues (RowIndex Absolute)
  }
  deriving (Eq, Ord, Show, Generic)

type ArithmeticCircuit = Circuit PolynomialConstraints Polynomial

type LogicCircuit = Circuit LogicConstraints Term
