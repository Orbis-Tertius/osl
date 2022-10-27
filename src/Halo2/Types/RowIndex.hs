{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.RowIndex
  ( RowIndex (RowIndex, getRowIndex),
    RowIndexType (Relative, Absolute),
  )
where

import Halo2.Prelude

data RowIndexType = Relative | Absolute

type RowIndex :: RowIndexType -> Type
newtype RowIndex a = RowIndex {getRowIndex :: Int}
  deriving (Num, Enum, Real, Integral, Eq, Ord, Show, Generic)
