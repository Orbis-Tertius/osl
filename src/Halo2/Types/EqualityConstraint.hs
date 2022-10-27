{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.EqualityConstraint (EqualityConstraint (EqualityConstraint, getEqualityConstraint)) where

import Halo2.Prelude
import Halo2.Types.CellReference

-- TODO: distinguish absolute and relative cell references
-- at type level
newtype EqualityConstraint = EqualityConstraint
  {getEqualityConstraint :: Set CellReference}
  deriving (Eq, Ord, Generic, Show)
