{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Byte
  ( Byte (Byte),
  )
where

import Halo2.Prelude

newtype Byte = Byte {unByte :: Integer}
  deriving (Generic)
