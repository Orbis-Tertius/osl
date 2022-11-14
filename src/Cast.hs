{-# LANGUAGE OverloadedStrings #-}

module Cast
  ( intToInteger,
    word64ToInteger,
    integerToInt,
    integerToWord64,
    scalarToInt,
  )
where

import Data.Bits (toIntegralSized)
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Die (die)
import Stark.Types.Scalar (Scalar, toWord64)

intToInteger :: Int -> Integer
intToInteger = fromMaybe (die "intToInteger partiality") . toIntegralSized

word64ToInteger :: Word64 -> Integer
word64ToInteger = fromMaybe (die "word64ToInteger partiality") . toIntegralSized

integerToInt :: Integer -> Maybe Int
integerToInt = toIntegralSized

integerToWord64 :: Integer -> Maybe Word64
integerToWord64 = toIntegralSized

scalarToInt :: Scalar -> Int
scalarToInt = fromMaybe (die "scalarToInt partiality") . toIntegralSized . toWord64
