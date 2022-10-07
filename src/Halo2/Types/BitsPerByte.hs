{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.BitsPerByte (BitsPerByte (BitsPerByte)) where

import Halo2.Prelude

newtype BitsPerByte = BitsPerByte {unBitsPerByte :: Int}
  deriving (Generic)
