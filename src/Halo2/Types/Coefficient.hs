{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Coefficient (Coefficient (Coefficient, getCoefficient)) where

import Halo2.Prelude
import Stark.Types.Scalar (Scalar, scalarToInteger)

newtype Coefficient = Coefficient {getCoefficient :: Scalar}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Enum, Num)

instance Show Coefficient where
  show = show . scalarToInteger . getCoefficient
