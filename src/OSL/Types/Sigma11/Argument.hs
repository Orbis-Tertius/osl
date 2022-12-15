{-# LANGUAGE DeriveGeneric #-}

module OSL.Types.Sigma11.Argument
  ( Argument (Argument),
    Statement (Statement),
    Witness (Witness),
  ) where

import GHC.Generics (Generic)
import OSL.Types.Sigma11.Value (Value)

data Argument =
  Argument
  { statement :: Statement,
    witness :: Witness
  }
  deriving Generic

newtype Statement =
  Statement { unStatement :: [Value] }
  deriving Generic

newtype Witness =
  Witness { unWitness :: [Value] }
  deriving Generic
