{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLabels #-}


module Halo2.ArithmetizationConfig
  ( getArithmetizationConfig
  , getByteDecompositionSize
  ) where


import Cast (intToInteger)
import Control.Lens ((^.))
import Crypto.Number.Basic (numBits)
import Halo2.Prelude
import Halo2.Types.ArithmetizationConfig (ArithmetizationConfig (..))
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.ByteDecompositionSize (ByteDecompositionSize (..))
import Halo2.Types.BytesPerWord (BytesPerWord (..))
import Halo2.Types.FiniteField (FiniteField (..))
import Halo2.Types.FixedBound (FixedBound (..))


getArithmetizationConfig :: FiniteField -> BitsPerByte -> ArithmetizationConfig
getArithmetizationConfig finiteField bitsPerByte =
  ArithmetizationConfig
  bitsPerByte
  (getBytesPerWord finiteField bitsPerByte)
  finiteField


getBytesPerWord :: FiniteField -> BitsPerByte -> BytesPerWord
getBytesPerWord (FiniteField fieldSize) (BitsPerByte bitsPerByte) =
  case numBits (intToInteger fieldSize) `quotRem` bitsPerByte of
    (q, 0) -> BytesPerWord q
    (q, _) -> BytesPerWord (q+1)


getByteDecompositionSize :: ArithmetizationConfig -> FixedBound -> ByteDecompositionSize
getByteDecompositionSize config (FixedBound b) =
  case numBits (intToInteger b) `quotRem` (config ^. #bitsPerByte . #unBitsPerByte) of
    (q, 0) -> ByteDecompositionSize q
    (q, _) -> ByteDecompositionSize (q+1)
