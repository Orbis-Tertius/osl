{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.ColumnTypes
  ( ColumnTypes (ColumnTypes, getColumnTypes),
    fromList,
  )
where

import qualified Data.Map as Map
import Halo2.Prelude
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType)

newtype ColumnTypes = ColumnTypes
  {getColumnTypes :: Map ColumnIndex ColumnType}
  deriving (Eq, Ord, Show, Generic, Semigroup, Monoid)

fromList :: [ColumnType] -> ColumnTypes
fromList = ColumnTypes . Map.fromList . zip [0 ..]
