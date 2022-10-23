{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.WitnessGenerationContext (WitnessGenerationContext (WitnessGenerationContext)) where

import Halo2.Prelude
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Stark.Types.Scalar (Scalar)

newtype WitnessGenerationContext = WitnessGenerationContext
  { getWitnessGenerationContext ::
      Map PolynomialVariable Scalar
  }
  deriving (Eq, Ord, Show, Generic)
