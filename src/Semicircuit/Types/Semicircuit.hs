{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Semicircuit.Types.Semicircuit
  ( Semicircuit (Semicircuit),
    FreeVariables (..),
    FunctionCalls (..),
    FunctionCall (FunctionCall),
    IndicatorFunctionCalls (..),
    IndicatorFunctionCall (..),
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
    indicatorCalls :: IndicatorFunctionCalls,
    functionCalls :: FunctionCalls,
    adviceTerms :: AdviceTerms,
    formula :: Formula
  }
  deriving (Generic, Show)

newtype FreeVariables = FreeVariables {unFreeVariables :: Set Name}
  deriving (Generic, Show)

newtype IndicatorFunctionCalls = IndicatorFunctionCalls
  { unIndicatorFunctionCalls ::
      Set IndicatorFunctionCall
  }
  deriving newtype (Semigroup, Monoid)
  deriving stock (Generic, Show)

newtype FunctionCalls = FunctionCalls {unFunctionCalls :: Set FunctionCall}
  deriving newtype (Semigroup, Monoid)
  deriving stock (Generic, Show)

newtype AdviceTerms = AdviceTerms {unAdviceTerms :: Set Term}
  deriving newtype (Semigroup, Monoid)
  deriving stock (Generic, Show)

data IndicatorFunctionCall
  = IndicatorFunctionCall Term Term
  deriving (Eq, Ord, Show)

data FunctionCall = FunctionCall
  { name :: Name,
    args :: NonEmpty Term
  }
  deriving (Eq, Ord, Generic, Show)
