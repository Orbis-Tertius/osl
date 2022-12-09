{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Argument
  ( Argument (Argument),
    Statement (Statement),
    Witness (Witness),
  )
where

import GHC.Generics (Generic)
import OSL.Types.Value (Value)

data Argument = Argument
  { statement :: Statement,
    witness :: Witness
  }
  deriving stock (Eq, Ord, Generic, Show)

newtype Statement = Statement {unStatement :: Value}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)

newtype Witness = Witness {unWitness :: Value}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)
