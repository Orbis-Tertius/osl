{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LogicConstraints
  ( LogicConstraints (LogicConstraints),
  )
where

import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.FixedBound (FixedBound)
import Halo2.Types.Label (Label)
import Halo2.Types.LogicConstraint (LogicConstraint)

data LogicConstraints = LogicConstraints
  { constraints :: [(Label, LogicConstraint)],
    bounds :: Map ColumnIndex FixedBound
  }
  deriving (Generic, Show)

instance Semigroup LogicConstraints where
  (LogicConstraints a b) <> (LogicConstraints c d) =
    LogicConstraints (a <> c) (b <> d)

instance Monoid LogicConstraints where
  mempty = LogicConstraints mempty mempty
