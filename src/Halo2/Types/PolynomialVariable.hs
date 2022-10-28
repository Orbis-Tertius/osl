{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.PolynomialVariable (PolynomialVariable (PolynomialVariable)) where

import Halo2.Prelude
import Halo2.Types.ColumnIndex
import Halo2.Types.RowIndex

data PolynomialVariable = PolynomialVariable
  { colIndex :: ColumnIndex,
    rowIndex :: RowIndex 'Relative
  }
  deriving (Eq, Ord, Generic)

instance Show PolynomialVariable where
  show x = "x" <> show (x ^. #colIndex) <> "," <> show (x ^. #rowIndex)
