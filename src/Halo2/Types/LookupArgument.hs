{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LookupArgument (LookupArgument (LookupArgument)) where

import Halo2.Prelude
import Halo2.Types.InputExpression (InputExpression)
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import Halo2.Types.Polynomial (Polynomial)

data LookupArgument = LookupArgument
  { gate :: Polynomial,
    tableMap :: [(InputExpression, LookupTableColumn)]
  }
  deriving (Eq, Ord, Show, Generic)
