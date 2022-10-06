{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LogicConstraints
  ( LogicConstraints (LogicConstraints),
  )
where

import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.FixedBound (FixedBound)
import Halo2.Types.LogicConstraint (LogicConstraint)

data LogicConstraints = LogicConstraints
  { constraints :: [LogicConstraint],
    bounds :: Map ColumnIndex FixedBound
  }
  deriving (Generic)
