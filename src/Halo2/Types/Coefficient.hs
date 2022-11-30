{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Coefficient (Coefficient (Coefficient, getCoefficient)) where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Halo2.Prelude
import Stark.Types.Scalar (Scalar, scalarToInteger)

newtype Coefficient = Coefficient {getCoefficient :: Scalar}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Group.C, Ring.C)

instance Show Coefficient where
  show = show . scalarToInteger . getCoefficient
