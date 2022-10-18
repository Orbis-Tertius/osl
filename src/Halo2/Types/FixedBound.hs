{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedBound
  ( FixedBound (FixedBound),
  )
where

import Halo2.Prelude

newtype FixedBound = FixedBound
  {unFixedBound :: Integer}
  deriving (Generic)
