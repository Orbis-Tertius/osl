{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.ByteDecomposition
  ( decomposeBytes,
    composeBytes,
    countBytes,
  )
where

import Cast (intToInteger)
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Byte (Byte (..))
import Halo2.Types.ByteDecomposition (ByteDecomposition (..))
import Halo2.Types.FixedBound (FixedBound (..))
import Stark.Types.Scalar (Scalar, scalarToInteger)

decomposeBytes :: BitsPerByte -> Scalar -> ByteDecomposition
decomposeBytes (BitsPerByte b) x =
  case scalarToInteger x `quotRem` (2 ^ b) of
    (0, r) -> ByteDecomposition [Byte (fromInteger r)]
    (x', r) ->
      decomposeBytes (BitsPerByte b) (fromInteger x')
        <> ByteDecomposition [Byte (fromInteger r)]

composeBytes :: BitsPerByte -> ByteDecomposition -> Scalar
composeBytes _ (ByteDecomposition []) = 0
composeBytes (BitsPerByte b) (ByteDecomposition (Byte x : xs)) =
  (x * (2 ^ intToInteger (b * length xs)))
    + composeBytes (BitsPerByte b) (ByteDecomposition xs)

countBytes :: BitsPerByte -> FixedBound -> Int
countBytes bits (FixedBound b) =
  length . (^. #unByteDecomposition) $
    decomposeBytes bits (b - 1)
