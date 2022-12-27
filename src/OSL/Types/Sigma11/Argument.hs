{-# LANGUAGE DeriveGeneric #-}

module OSL.Types.Sigma11.Argument
  ( Argument (Argument),
    Statement (Statement),
    Witness (Witness),
  )
where

import GHC.Generics (Generic)
import OSL.Types.Sigma11.Value (Value)
import OSL.Types.Sigma11.ValueTree (ValueTree)

data Argument = Argument
  { statement :: Statement,
    witness :: Witness
  }
  deriving (Show, Generic)

newtype Statement = Statement {unStatement :: [Value]}
  deriving (Show, Generic)

newtype Witness = Witness {unWitness :: ValueTree}
  deriving (Show, Generic)
