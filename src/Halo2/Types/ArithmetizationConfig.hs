{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.ArithmetizationConfig
  ( ArithmetizationConfig (ArithmetizationConfig),
  )
where

import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte)
import Halo2.Types.BytesPerWord (BytesPerWord)
import Halo2.Types.FiniteField (FiniteField)

data ArithmetizationConfig = ArithmetizationConfig
  { bitsPerByte :: BitsPerByte,
    bytesPerWord :: BytesPerWord,
    field :: FiniteField
  }
  deriving (Generic)
