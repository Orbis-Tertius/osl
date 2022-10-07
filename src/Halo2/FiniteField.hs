{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.FiniteField
  ( plus,
    times,
    reciprocal,
    half,
    one,
    zero,
    minusOne,
  )
where

import Cast (intToInteger)
import Data.Maybe (fromMaybe)
import Die (die)
import Halo2.Prelude
import Halo2.Types.FieldElement (FieldElement (..))
import Halo2.Types.FiniteField (FiniteField (..))

plus :: FiniteField -> FieldElement -> FieldElement -> FieldElement
plus (FiniteField n) (FieldElement a) (FieldElement b) =
  FieldElement ((a + b) `mod` intToInteger n)

times :: FiniteField -> FieldElement -> FieldElement -> FieldElement
times (FiniteField n) (FieldElement a) (FieldElement b) =
  FieldElement ((a * b) `mod` intToInteger n)

reciprocal :: FiniteField -> FieldElement -> Maybe FieldElement
reciprocal (FiniteField _n) (FieldElement _m) =
  Nothing -- TODO

half :: FiniteField -> FieldElement
half f =
  fromMaybe (die "could not compute 1/2") $
    reciprocal f 2

one :: FieldElement
one = FieldElement 1

zero :: FieldElement
zero = FieldElement 0

minusOne :: FiniteField -> FieldElement
minusOne (FiniteField n) =
  FieldElement (intToInteger (n - 1))
