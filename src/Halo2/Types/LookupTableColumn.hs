{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LookupTableColumn (LookupTableColumn (..)) where

import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)

newtype LookupTableColumn = LookupTableColumn {unLookupTableColumn :: ColumnIndex}
  deriving stock (Eq, Ord, Generic)
  deriving newtype Show
