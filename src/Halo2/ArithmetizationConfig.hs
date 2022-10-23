{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.ArithmetizationConfig
  ( getArithmetizationConfig,
    getByteDecompositionSize,
  )
where

import Cast (word64ToInteger)
import Crypto.Number.Basic (numBits)
import Halo2.Prelude
import Halo2.Types.ArithmetizationConfig (ArithmetizationConfig (..))
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.ByteDecompositionSize (ByteDecompositionSize (..))
import Halo2.Types.BytesPerWord (BytesPerWord (..))
import Halo2.Types.FixedBound (FixedBound (..))
import Stark.Types.Scalar (order, scalarToInteger)

getArithmetizationConfig :: BitsPerByte -> ArithmetizationConfig
getArithmetizationConfig bitsPerByte =
  ArithmetizationConfig
    bitsPerByte
    (getBytesPerWord bitsPerByte)

getBytesPerWord :: BitsPerByte -> BytesPerWord
getBytesPerWord (BitsPerByte bitsPerByte) =
  case numBits (word64ToInteger order) `quotRem` bitsPerByte of
    (q, 0) -> BytesPerWord q
    (q, _) -> BytesPerWord (q + 1)

getByteDecompositionSize :: ArithmetizationConfig -> FixedBound -> ByteDecompositionSize
getByteDecompositionSize config (FixedBound b) =
  case numBits (scalarToInteger b) `quotRem`
         (config ^. #bitsPerByte . #unBitsPerByte) of
    (q, 0) -> ByteDecompositionSize q
    (q, _) -> ByteDecompositionSize (q + 1)
