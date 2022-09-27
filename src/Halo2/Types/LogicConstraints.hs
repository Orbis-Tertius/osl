{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.LogicConstraints
  ( LogicConstraints (LogicConstraints)
  ) where


import Halo2.Prelude
import Halo2.Types.LogicConstraint (LogicConstraint)


newtype LogicConstraints = LogicConstraints
  { constraints :: [LogicConstraint]
  } deriving Generic
