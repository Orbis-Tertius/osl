{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.ArithmetizationConfig
  ( getArithmetizationConfig
  ) where


import Cast (intToInteger)
import Crypto.Number.Basic (numBits)
import Halo2.Prelude
import Halo2.Types.ArithmetizationConfig (ArithmetizationConfig (..))
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.BytesPerWord (BytesPerWord (..))
import Halo2.Types.FiniteField (FiniteField (..))


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
