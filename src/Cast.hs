{-# LANGUAGE OverloadedStrings #-}

module Cast
  ( intToInteger,
  )
where

import Data.Bits (toIntegralSized)
import Data.Maybe (fromMaybe)
import Die (die)

intToInteger :: Int -> Integer
intToInteger = fromMaybe (die "intToInteger partiality") . toIntegralSized
