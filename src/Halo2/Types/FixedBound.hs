{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Halo2.Types.FixedBound
  ( FixedBound (FixedBound),
    boolBound,
    integerToFixedBound,
    fixedBoundToInteger,
  )
where

import Cast (word64ToInteger, integerToWord64)
import Die (die)
import Data.Word (Word64)
import Halo2.Prelude
import Stark.Types.Scalar (order)

newtype FixedBound = FixedBound
  {unFixedBound :: Word64}
  deriving stock (Generic, Show)

instance Num FixedBound where
  a + b = integerToFixedBound (fixedBoundToInteger a + fixedBoundToInteger b)
  a * b = integerToFixedBound (fixedBoundToInteger a * fixedBoundToInteger b)
  abs = id
  signum = const 1
  fromInteger = integerToFixedBound
  negate = die "FixedBound.negate: not implemented"

fixedBoundToInteger :: FixedBound -> Integer
fixedBoundToInteger = word64ToInteger . unFixedBound

integerToFixedBound :: Integer -> FixedBound
integerToFixedBound k =
  case integerToWord64 (abs k `mod` word64ToInteger order) of
    Just w -> FixedBound w
    Nothing -> die "integerToFixedBound: constant term mod field size out of range of Word64 (this is a compiler bug)"


boolBound :: FixedBound
boolBound = FixedBound 2
