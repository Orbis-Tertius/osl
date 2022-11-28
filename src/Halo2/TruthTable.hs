{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.TruthTable
  ( getByteRangeColumn,
    getZeroIndicatorColumn,
  )
where

import Cast (intToInteger)
import Data.Maybe (fromMaybe)
import Data.Text (pack)
import Die (die)
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.FixedColumn (FixedColumn (..))
import Halo2.Types.RowCount (RowCount (..))
import Stark.Types.Scalar (Scalar, integerToScalar, scalarToInt)

getByteRangeColumn :: BitsPerByte -> RowCount -> FixedColumn
getByteRangeColumn (BitsPerByte b) (RowCount r) =
  let m' = (2 ^ b) - 1
      m =
        fromMaybe
          (die $ "getByteRangeColumn: " <> pack (show m') <> " out of range of scalar type")
          (integerToScalar (intToInteger m'))
   in FixedColumn ((f <$> [0 .. m']) <> replicate (scalarToInt r - m') m)
  where
    f :: Int -> Scalar
    f =
      fromMaybe (die "getByteRangeColumn: f partiality")
        . integerToScalar
        . intToInteger

getZeroIndicatorColumn :: RowCount -> FixedColumn
getZeroIndicatorColumn (RowCount n) =
  FixedColumn (1 : replicate (scalarToInt n - 1) 0)
