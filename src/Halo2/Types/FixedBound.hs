{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedBound
  ( FixedBound (FixedBound),
    boolBound,
    integerToFixedBound,
    fixedBoundToInteger,
  )
where

import Cast (integerToWord64, word64ToInteger)
import Data.Word (Word64)
import Die (die)
import Halo2.Prelude
import Stark.Types.Scalar (order)

newtype FixedBound = FixedBound
  {unFixedBound :: Word64}
  deriving stock (Generic)
  deriving newtype (Show)

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
  case integerToWord64 k of
    Just w -> if w < order then FixedBound w else FixedBound order
    Nothing -> FixedBound order

boolBound :: FixedBound
boolBound = FixedBound 2
