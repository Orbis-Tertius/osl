{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.PolynomialConstraints
  ( PolynomialConstraints (PolynomialConstraints)
  ) where


import           Halo2.Prelude
import           Halo2.Types.Polynomial (Polynomial)
import           Halo2.Types.PolynomialDegreeBound (PolynomialDegreeBound)


data PolynomialConstraints = PolynomialConstraints
  { constraints :: [Polynomial]
  , degreeBound :: PolynomialDegreeBound
  }
  deriving (Eq, Ord, Show, Generic)
