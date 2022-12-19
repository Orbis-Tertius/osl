{-# LANGUAGE DeriveGeneric #-}

module OSL.Types.Sigma11.ValueTree (ValueTree (ValueTree)) where

import GHC.Generics (Generic)
import OSL.Types.Sigma11.Value (Value)

data ValueTree =
  ValueTree
  { leaf :: Maybe Value,
    branches :: [ValueTree]
  }
  deriving (Show, Generic)
