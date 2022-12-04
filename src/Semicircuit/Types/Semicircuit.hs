{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Semicircuit.Types.Semicircuit
  ( Semicircuit (Semicircuit),
    FreeVariables (..),
    FunctionCalls (..),
    FunctionCall (FunctionCall),
    AdviceTerms (..),
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import GHC.Generics (Generic)
import Semicircuit.Types.PNFFormula (Formula)
import Semicircuit.Types.Sigma11 (Name, Term)

data Semicircuit = Semicircuit
  { freeVariables :: FreeVariables,
    functionCalls :: FunctionCalls,
    adviceTerms :: AdviceTerms,
    formula :: Formula
  }
  deriving (Generic, Show)

newtype FreeVariables = FreeVariables {unFreeVariables :: Set Name}
  deriving (Generic, Show)

newtype FunctionCalls = FunctionCalls {unFunctionCalls :: Set FunctionCall}
  deriving newtype (Semigroup, Monoid)
  deriving stock (Generic, Show)

newtype AdviceTerms = AdviceTerms {unAdviceTerms :: Set Term}
  deriving newtype (Semigroup, Monoid)
  deriving stock (Generic, Show)

data FunctionCall = FunctionCall
  { name :: Name,
    args :: NonEmpty Term
  }
  deriving (Eq, Ord, Generic, Show)
