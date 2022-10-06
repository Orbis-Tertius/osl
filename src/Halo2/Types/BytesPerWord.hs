{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.BytesPerWord (BytesPerWord (BytesPerWord)) where

import Halo2.Prelude

newtype BytesPerWord = BytesPerWord {unBytesPerWord :: Int}
  deriving (Generic)
