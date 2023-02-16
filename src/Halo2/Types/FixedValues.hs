{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedValues (FixedValues (FixedValues, getFixedValues)) where

import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.FixedColumn (FixedColumn)

newtype FixedValues a = FixedValues
  {getFixedValues :: Map ColumnIndex (FixedColumn a)}
  deriving (Eq, Ord, Generic, Show, Semigroup, Monoid)
