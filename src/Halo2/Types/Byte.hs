{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Byte
  ( Byte (Byte),
  )
where

import Halo2.Prelude
import Stark.Types.Scalar (Scalar)

newtype Byte = Byte {unByte :: Scalar}
  deriving (Generic)
