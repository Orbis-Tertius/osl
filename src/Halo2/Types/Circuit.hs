{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.Circuit ( Circuit (Circuit) ) where


import           Halo2.Prelude
import           Halo2.Types.EqualityConstraints (EqualityConstraints)
import           Halo2.Types.FixedVariableValues (FixedVariableValues)
import           Halo2.Types.RowCount            (RowCount)
import           Halo2.Types.ColumnTypes                  (ColumnTypes)
import           Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import           Halo2.Types.FiniteField                  (FiniteField)
import           Halo2.Types.LookupArguments              (LookupArguments)
import           Halo2.Types.PolynomialConstraints        (PolynomialConstraints)
import           Halo2.Types.PolynomialDegreeBound        (PolynomialDegreeBound)

data Circuit =
  Circuit
  { field                        :: FiniteField
  , columnTypes                  :: ColumnTypes
  , equalityConstrainableColumns :: EqualityConstrainableColumns
  , polynomialDegreeBound        :: PolynomialDegreeBound
  , polynomialConstraints        :: PolynomialConstraints
  , lookupArguments              :: LookupArguments
  , rowCount                     :: RowCount
  , equalityConstraints          :: EqualityConstraints
  , fixedVariableValues          :: FixedVariableValues
  }
  deriving (Eq, Ord, Show, Generic)
