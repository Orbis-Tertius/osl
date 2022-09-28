{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.ByteDecomposition
  ( decomposeBytes
  , composeBytes
  ) where


import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Byte (Byte (..))
import Halo2.Types.ByteDecomposition (ByteDecomposition (..))


decomposeBytes :: BitsPerByte -> FieldElement -> ByteDecomposition


composeBytes :: BitsPerByte -> ByteDecomposition -> FieldElement
