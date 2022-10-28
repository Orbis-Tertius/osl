{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLabels #-}

module Halo2.Types.LookupArgument (LookupArgument (LookupArgument)) where

import Data.List (intercalate)
import Halo2.Prelude
import Halo2.Types.InputExpression (InputExpression)
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import Halo2.Types.Polynomial (Polynomial)

data LookupArgument = LookupArgument
  { gate :: Polynomial,
    tableMap :: [(InputExpression, LookupTableColumn)]
  }
  deriving (Eq, Ord, Generic)

instance Show LookupArgument where
  show arg =
    show (arg ^. #gate) <> " = 0 => ("
      <> intercalate ", " (show <$> inputs)
      <> " ∈ (" <> intercalate ", " (show <$> cols) <> ")"
    where
      (inputs, cols) = unzip (arg ^. #tableMap)
