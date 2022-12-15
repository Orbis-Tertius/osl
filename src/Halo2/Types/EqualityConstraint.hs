{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.EqualityConstraint (EqualityConstraint (EqualityConstraint, getEqualityConstraint)) where

import Data.List (intercalate)
import Data.Set (toList)
import Halo2.Prelude
import Halo2.Types.CellReference

newtype EqualityConstraint = EqualityConstraint
  {getEqualityConstraint :: Set CellReference}
  deriving (Eq, Ord, Generic)

instance Show EqualityConstraint where
  show xs = intercalate " = " (show <$> toList (getEqualityConstraint xs))
