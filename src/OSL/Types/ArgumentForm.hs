{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.ArgumentForm
  ( ArgumentForm (ArgumentForm),
    StatementType (StatementType),
    WitnessType (WitnessType),
  )
where

import GHC.Generics (Generic)
import OSL.Types.OSL (Type (Fin, Product))

data ArgumentForm = ArgumentForm
  { statementType :: StatementType,
    witnessType :: WitnessType
  }
  deriving stock (Eq, Ord, Generic, Show)

newtype StatementType = StatementType {unStatementType :: Type ()}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)

instance Semigroup StatementType where
  StatementType (Fin () 1) <> b = b
  a <> StatementType (Fin () 1) = a
  StatementType a <> StatementType b =
    StatementType (Product () a b)

instance Monoid StatementType where
  mempty = StatementType (Fin () 1)

newtype WitnessType = WitnessType {unWitnessType :: Type ()}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)

instance Semigroup WitnessType where
  WitnessType (Fin () 1) <> b = b
  a <> WitnessType (Fin () 1) = a
  WitnessType a <> WitnessType b =
    WitnessType (Product () a b)

instance Monoid WitnessType where
  mempty = WitnessType (Fin () 1)
