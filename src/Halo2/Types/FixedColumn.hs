{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedColumn (FixedColumn (..)) where

import Halo2.Prelude
import Stark.Types.Scalar (Scalar)

newtype FixedColumn a = FixedColumn {unFixedColumn :: Map a Scalar}
  deriving (Eq, Ord, Generic, Show)
