{-# LANGUAGE OverloadedStrings #-}

module Cast
  ( intToInteger,
    word64ToInteger,
    integerToInt,
  )
where

import Data.Bits (toIntegralSized)
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Die (die)

intToInteger :: Int -> Integer
intToInteger = fromMaybe (die "intToInteger partiality") . toIntegralSized

word64ToInteger :: Word64 -> Integer
word64ToInteger = fromMaybe (die "word64ToInteger partiality") . toIntegralSized

integerToInt :: Integer -> Maybe Int
integerToInt = toIntegralSized
