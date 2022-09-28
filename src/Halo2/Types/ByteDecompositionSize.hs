{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.ByteDecompositionSize
  ( ByteDecompositionSize (ByteDecompositionSize)
  ) where


import Halo2.Prelude


newtype ByteDecompositionSize =
  ByteDecompositionSize
  { unByteDecompositionSize :: Int }
  deriving Generic
