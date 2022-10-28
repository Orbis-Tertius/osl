{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Coefficient (Coefficient (Coefficient, getCoefficient)) where

import Halo2.Prelude
import Stark.Types.Scalar (Scalar)

newtype Coefficient = Coefficient {getCoefficient :: Scalar}
  deriving (Enum, Eq, Ord, Show, Generic, Num)
