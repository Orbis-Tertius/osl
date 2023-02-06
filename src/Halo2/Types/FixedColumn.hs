{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedColumn (FixedColumn (..)) where

import Halo2.Prelude
import Stark.Types.Scalar (Scalar, scalarToInteger)

-- TODO: choose a more efficient data structure
-- (maybe vectors?)
newtype FixedColumn = FixedColumn {unFixedColumn :: [Scalar]}
  deriving (Eq, Ord, Generic)

instance Show FixedColumn where
  show = show . fmap scalarToInteger . unFixedColumn
