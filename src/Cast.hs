{-# LANGUAGE OverloadedStrings #-}

module Cast
  ( intToInteger,
    word64ToInteger,
    integerToInt,
    integerToWord64,
    integerToRatio,
    word8ToInteger,
    word64ToRatio,
  )
where

import Data.Bits (toIntegralSized)
import Data.Maybe (fromMaybe)
import Data.Word (Word64, Word8)
import Die (die)

intToInteger :: Int -> Integer
intToInteger = fromMaybe (die "intToInteger partiality") . toIntegralSized

word64ToInteger :: Word64 -> Integer
word64ToInteger = fromMaybe (die "word64ToInteger partiality") . toIntegralSized

integerToInt :: Integer -> Maybe Int
integerToInt = toIntegralSized

integerToWord64 :: Integer -> Maybe Word64
integerToWord64 = toIntegralSized

integerToRatio :: Integer -> Rational
integerToRatio = toRational

word8ToInteger :: Word8 -> Integer
word8ToInteger = fromMaybe (die "word8ToInteger partiality") . toIntegralSized

word64ToRatio :: Word64 -> Rational
word64ToRatio = integerToRatio . fromMaybe (die "word64ToRatio partiality") . toIntegralSized
