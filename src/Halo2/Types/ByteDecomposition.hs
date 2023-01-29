{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.ByteDecomposition
  ( ByteDecomposition (ByteDecomposition),
  )
where

import Halo2.Prelude
import Halo2.Types.Byte (Byte)
import Halo2.Types.Sign (Sign)

data ByteDecomposition = ByteDecomposition
  { sign :: Sign,
    -- Most significant byte first
    bytes :: [Byte]
  }
  deriving (Show, Generic)
