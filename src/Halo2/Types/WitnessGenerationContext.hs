{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude          #-}


module Halo2.Types.WitnessGenerationContext ( WitnessGenerationContext (WitnessGenerationContext ) ) where


import           Halo2.Prelude
import           Halo2.Types.FieldElement       (FieldElement)
import           Halo2.Types.PolynomialVariable (PolynomialVariable)


newtype WitnessGenerationContext =
  WitnessGenerationContext
  { getWitnessGenerationContext
    :: Map PolynomialVariable FieldElement }
  deriving (Eq, Ord, Show, Generic)
