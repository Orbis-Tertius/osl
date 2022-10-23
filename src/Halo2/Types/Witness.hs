{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Witness (Witness (Witness)) where

import Halo2.Prelude
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Stark.Types.Scalar (Scalar)

newtype Witness = Witness
  { getWitness ::
      Map PolynomialVariable Scalar
  }
  deriving (Eq, Ord, Show, Generic)
