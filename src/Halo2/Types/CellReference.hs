{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}

module Halo2.Types.CellReference
  ( CellReference (CellReference)
  ) where


import Halo2.Prelude
import Halo2.Types.ColumnIndex
import Halo2.Types.RowIndex


data CellReference = CellReference
  { colIndex :: ColumnIndex
  , rowIndex :: RowIndex 'Absolute
  }
  deriving (Eq, Ord, Show, Generic)
