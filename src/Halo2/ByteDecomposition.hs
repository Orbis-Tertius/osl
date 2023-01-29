{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.ByteDecomposition
  ( decomposeBytes,
    composeBytes,
    countBytes,
    applySign,
  )
where

import qualified Algebra.Additive as Group
import Cast (intToInteger)
import Data.Maybe (fromMaybe)
import Die (die)
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Byte (Byte (..))
import Halo2.Types.ByteDecomposition (ByteDecomposition (..))
import Halo2.Types.FixedBound (FixedBound (..))
import Halo2.Types.Sign (Sign (Negative, Positive))
import Stark.Types.Scalar (Scalar, fromWord64, integerToScalar, normalize, scalarToInteger)

-- Splits a scalar its into sign and its unsigned part, based on the idea
-- that if x > |F|/2, then x is negative.
getSignAndUnsignedPart :: Scalar -> (Sign, Scalar)
getSignAndUnsignedPart x =
  let x' = Group.negate x
   in if x' < x
        then (Negative, x')
        else (Positive, x)

decomposeBytes :: BitsPerByte -> Scalar -> ByteDecomposition
decomposeBytes bitsPerByte (normalize -> x) =
  let (s, x') = getSignAndUnsignedPart x
   in ByteDecomposition s (decomposeBytesPositive bitsPerByte x')

-- Assumes the given scalar is positive and breaks it down into bytes.
decomposeBytesPositive :: BitsPerByte -> Scalar -> [Byte]
decomposeBytesPositive (BitsPerByte b) x =
  let (x', r) = scalarToInteger x `quotRem` (2 ^ b)
   in if x' == 0
        then [Byte (f r)]
        else
          rec (f x')
            <> [Byte (f r)]
  where
    rec = decomposeBytesPositive (BitsPerByte b)

    f :: Integer -> Scalar
    f =
      fromMaybe (die "decomposeBytes: byte out of range of scalar type")
        . integerToScalar

composeBytes :: BitsPerByte -> ByteDecomposition -> Scalar
composeBytes bitsPerByte (ByteDecomposition s bs) =
  applySign s $
    composeBytesPositive bitsPerByte bs

composeBytesPositive :: BitsPerByte -> [Byte] -> Scalar
composeBytesPositive _ [] = 0
composeBytesPositive (BitsPerByte b) (Byte x : xs) =
  (x * (2 ^ intToInteger (b * length xs)))
    + composeBytesPositive (BitsPerByte b) xs

applySign :: Sign -> Scalar -> Scalar
applySign =
  \case
    Positive -> id
    Negative -> Group.negate

countBytes :: BitsPerByte -> FixedBound -> Int
countBytes bits (FixedBound b) =
  length . (^. #bytes) $
    decomposeBytes
      bits
      ( fromMaybe
          (die "countBytes: bound out of range (this is a compiler bug)")
          (fromWord64 (b - 1))
      )
