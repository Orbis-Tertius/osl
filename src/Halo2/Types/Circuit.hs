{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.Circuit
  ( Circuit (Circuit)
  , ArithmeticCircuit
  , LogicCircuit
  ) where


import           Halo2.Prelude
import           Halo2.Types.EqualityConstraints (EqualityConstraints)
import           Halo2.Types.FixedValues         (FixedValues)
import           Halo2.Types.RowCount            (RowCount)
import           Halo2.Types.ColumnTypes                  (ColumnTypes)
import           Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import           Halo2.Types.FiniteField                  (FiniteField)
import           Halo2.Types.LogicConstraints             (LogicConstraints)
import           Halo2.Types.LookupArguments              (LookupArguments)
import           Halo2.Types.PolynomialConstraints        (PolynomialConstraints)


data Circuit a =
  Circuit
  { field                        :: FiniteField
  , columnTypes                  :: ColumnTypes
  , equalityConstrainableColumns :: EqualityConstrainableColumns
  , gateConstraints              :: a
  , lookupArguments              :: LookupArguments
  , rowCount                     :: RowCount
  , equalityConstraints          :: EqualityConstraints
  , fixedValues                  :: FixedValues
  }
  deriving (Eq, Ord, Show, Generic)


type ArithmeticCircuit = Circuit PolynomialConstraints


type LogicCircuit = Circuit LogicConstraints
