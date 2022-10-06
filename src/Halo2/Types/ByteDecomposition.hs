{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.ByteDecomposition
  ( ByteDecomposition (ByteDecomposition),
  )
where

import Halo2.Prelude
import Halo2.Types.Byte (Byte)

-- Most significant byte first
newtype ByteDecomposition = ByteDecomposition
  {unByteDecomposition :: [Byte]}
  deriving (Semigroup, Monoid, Generic)
