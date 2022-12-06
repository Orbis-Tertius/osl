{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.ArgumentForm
  ( ArgumentForm (ArgumentForm),
    StatementType (StatementType),
    WitnessType (WitnessType)
  ) where

import GHC.Generics (Generic)
import OSL.Types.OSL (Type)

data ArgumentForm =
  ArgumentForm
  { statementType :: StatementType,
    witnessType :: WitnessType
  }
  deriving stock (Eq, Ord, Generic, Show)

newtype StatementType =
  StatementType { unStatementType :: Type () }
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)

newtype WitnessType =
  WitnessType { unWitnessType :: Type () }
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)
