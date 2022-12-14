{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.ByteDecomposition
  ( decomposeBytes,
    composeBytes,
    countBytes,
  )
where

import Cast (intToInteger)
import Data.Maybe (fromMaybe)
import Die (die)
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Byte (Byte (..))
import Halo2.Types.ByteDecomposition (ByteDecomposition (..))
import Halo2.Types.FixedBound (FixedBound (..))
import Stark.Types.Scalar (Scalar, fromWord64, integerToScalar, scalarToInteger)

decomposeBytes :: BitsPerByte -> Scalar -> ByteDecomposition
decomposeBytes (BitsPerByte b) x =
  let (x', r) = scalarToInteger x `quotRem` (2 ^ b)
   in if x' == 0
        then ByteDecomposition [Byte (f r)]
        else
          decomposeBytes (BitsPerByte b) (f x')
            <> ByteDecomposition [Byte (f r)]
  where
    f :: Integer -> Scalar
    f =
      fromMaybe (die "decomposeBytes: byte out of range of scalar type")
        . integerToScalar

composeBytes :: BitsPerByte -> ByteDecomposition -> Scalar
composeBytes _ (ByteDecomposition []) = 0
composeBytes (BitsPerByte b) (ByteDecomposition (Byte x : xs)) =
  (x * (2 ^ intToInteger (b * length xs)))
    + composeBytes (BitsPerByte b) (ByteDecomposition xs)

countBytes :: BitsPerByte -> FixedBound -> Int
countBytes bits (FixedBound b) =
  length . (^. #unByteDecomposition) $
    decomposeBytes
      bits
      ( fromMaybe
          (die "countBytes: bound out of range (this is a compiler bug)")
          (fromWord64 (b - 1))
      )
