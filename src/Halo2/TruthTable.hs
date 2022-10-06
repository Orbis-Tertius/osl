{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.TruthTable
  ( getByteRangeColumn,
    getZeroIndicatorColumn,
  )
where

import Cast (intToInteger)
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.FieldElement (FieldElement (..))
import Halo2.Types.FixedColumn (FixedColumn (..))
import Halo2.Types.RowCount (RowCount (..))

getByteRangeColumn :: BitsPerByte -> RowCount -> FixedColumn
getByteRangeColumn (BitsPerByte b) (RowCount r) =
  let m = (2 ^ b) - 1
      m' = FieldElement (intToInteger m)
   in FixedColumn ([0 .. m'] <> replicate (r - m) m')

getZeroIndicatorColumn :: RowCount -> FixedColumn
getZeroIndicatorColumn (RowCount n) =
  FixedColumn (1 : replicate (n - 1) 0)
