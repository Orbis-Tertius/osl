{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Halo2.Types.Label (Label (Label)) where

import Data.String (IsString)
import GHC.Generics (Generic)

newtype Label = Label { unLabel :: String }
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show, IsString)
