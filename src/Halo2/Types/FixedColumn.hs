{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedColumn (FixedColumn (..)) where

import Halo2.Prelude
import Halo2.Types.FieldElement (FieldElement)

newtype FixedColumn = FixedColumn {unFixedColumn :: [FieldElement]}
  deriving (Eq, Ord, Generic, Show)
