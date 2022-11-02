{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.FixedBound
  ( FixedBound (FixedBound),
    boolBound,
  )
where

import Data.Word (Word64)
import Halo2.Prelude

newtype FixedBound = FixedBound
  {unFixedBound :: Word64}
  deriving stock (Generic, Show)
  deriving newtype Num

boolBound :: FixedBound
boolBound = FixedBound 2
