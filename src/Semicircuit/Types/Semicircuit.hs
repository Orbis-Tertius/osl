{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Semicircuit.Types.Semicircuit
  ( Semicircuit (..),
    FunctionCalls (..),
    FunctionCall (..),
    IndicatorFunctionCalls (..),
    IndicatorFunctionCall (..),
    AdviceTerms (..),
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import Semicircuit.Types.PNFFormula (Formula)
import Semicircuit.Types.Sigma11 (Name, Term)

data Semicircuit
  = Semicircuit
      IndicatorFunctionCalls
      FunctionCalls
      AdviceTerms
      Formula

newtype IndicatorFunctionCalls
  = IndicatorFunctionCalls
    { unIndicatorFunctionCalls
      :: Set IndicatorFunctionCall }
  deriving newtype (Semigroup, Monoid)

newtype FunctionCalls
  = FunctionCalls { unFunctionCalls :: Set FunctionCall }
  deriving newtype (Semigroup, Monoid)

newtype AdviceTerms
  = AdviceTerms { unAdviceTerms :: Set Term }
  deriving newtype (Semigroup, Monoid)

data IndicatorFunctionCall
  = IndicatorFunctionCall Term Term
  deriving (Eq, Ord)

data FunctionCall
  = FunctionCall Name (NonEmpty Term)
  deriving (Eq, Ord)
