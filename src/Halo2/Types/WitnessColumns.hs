{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.WitnessColumns ( WitnessColumns (WitnessColumns) ) where


import           Halo2.Prelude
import           Halo2.Types.ColumnIndex (ColumnIndex)


-- A witness column is one of the columns which is
-- generated from the inputs to the proving process
-- as part of the proving process.
-- Each witness column must be an advice column.
-- See also: CircuitWithWitnesses.
newtype WitnessColumns = WitnessColumns { getWitnessColumns :: Set ColumnIndex }
  deriving (Eq, Ord, Show, Generic)
