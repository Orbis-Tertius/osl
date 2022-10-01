{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}


module Halo2.FiniteField (reciprocal, half) where


import Data.Maybe (fromMaybe)

import Die (die)
import Halo2.Prelude
import Halo2.Types.FiniteField (FiniteField (..))
import Halo2.Types.FieldElement (FieldElement (..))


reciprocal :: FiniteField -> FieldElement -> Maybe FieldElement
reciprocal (FiniteField _n) (FieldElement _m) =
  Nothing -- todo


half :: FiniteField -> FieldElement
half f = fromMaybe (die "could not compute 1/2")
  $ reciprocal f 2
