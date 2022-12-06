{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LookupArgument (LookupArgument (LookupArgument)) where

import Data.List (intercalate)
import Halo2.Prelude
import Halo2.Types.InputExpression (InputExpression)
import Halo2.Types.LookupTableColumn (LookupTableColumn)

data LookupArgument a = LookupArgument
  { gate :: a,
    tableMap :: [(InputExpression a, LookupTableColumn)]
  }
  deriving (Eq, Ord, Generic)

instance Show a => Show (LookupArgument a) where
  show arg =
    show (arg ^. #gate) <> " = 0 => ("
      <> intercalate ", " (show <$> inputs)
      <> ") ∈ ("
      <> intercalate ", " (show <$> cols)
      <> ")"
    where
      (inputs, cols) = unzip (arg ^. #tableMap)
