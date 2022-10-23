{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Halo2.TruthTable
  ( getByteRangeColumn,
    getZeroIndicatorColumn,
  )
where

import Cast (integerToInt)
import Data.Maybe (fromMaybe)
import Die (die)
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.FixedColumn (FixedColumn (..))
import Halo2.Types.RowCount (RowCount (..))
import Stark.Types.Scalar (scalarToInteger)

getByteRangeColumn :: BitsPerByte -> RowCount -> FixedColumn
getByteRangeColumn (BitsPerByte b) (RowCount r) =
  let m = (2 ^ b) - 1
      m' = fromMaybe (die "getByteRangeColumn: m > maxBound @Int")
           $ integerToInt (scalarToInteger m)
   in FixedColumn ([0 .. m] <> replicate (r - m') m)

getZeroIndicatorColumn :: RowCount -> FixedColumn
getZeroIndicatorColumn (RowCount n) =
  FixedColumn (1 : replicate (n - 1) 0)
