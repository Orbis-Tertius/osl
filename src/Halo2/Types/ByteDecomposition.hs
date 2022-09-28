{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.ByteDecomposition
  ( ByteDecomposition (ByteDecomposition)
  ) where


import Halo2.Prelude
import Halo2.Types.Byte (Byte)


newtype ByteDecomposition =
  ByteDecomposition
  { unByteDecomposition :: [Byte] }
  deriving Generic
