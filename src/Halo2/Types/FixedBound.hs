{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedBound
  ( FixedBound (FixedBound),
    boolBound,
  )
where

import Halo2.Prelude
import Stark.Types.Scalar (Scalar)

newtype FixedBound = FixedBound
  {unFixedBound :: Scalar}
  deriving (Generic, Show)

boolBound :: FixedBound
boolBound = FixedBound 2
