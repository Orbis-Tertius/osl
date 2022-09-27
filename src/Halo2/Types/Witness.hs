{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude          #-}


module Halo2.Types.Witness ( Witness (Witness) ) where


import           Halo2.Prelude
import           Halo2.Types.FieldElement       (FieldElement)
import           Halo2.Types.PolynomialVariable (PolynomialVariable)


data Witness =
  Witness
  { getWitness
    :: Map PolynomialVariable FieldElement }
  deriving (Eq, Ord, Show, Generic)
