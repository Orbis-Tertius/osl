{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Exponent (Exponent (Exponent, getExponent)) where

import Halo2.Prelude

newtype Exponent = Exponent {getExponent :: Int}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Num, Enum, Real, Integral, Show)
