{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Coefficient
  ( plus
  , times
  , one
  , zero
  ) where


import qualified Halo2.FiniteField as F
import Halo2.Types.FieldElement (FieldElement (..))
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.Coefficient (Coefficient (..))


plus :: FiniteField -> Coefficient -> Coefficient -> Coefficient
plus f (Coefficient a) (Coefficient b) =
  Coefficient (F.plus f a b)


times :: FiniteField -> Coefficient -> Coefficient -> Coefficient
times f (Coefficient a) (Coefficient b) =
  Coefficient (F.times f a b)


one :: Coefficient
one = Coefficient (FieldElement 1)


zero :: Coefficient
zero = Coefficient (FieldElement 0)
