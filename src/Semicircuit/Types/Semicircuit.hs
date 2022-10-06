module Semicircuit.Types.Semicircuit
  ( Semicircuit (..),
    FunctionCalls (..),
    FunctionCall (..),
    IndicatorFunctionCalls (..),
    IndicatorFunctionCall (..),
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import OSL.Types.Sigma11 (Name, Term)
import Semicircuit.Types.PNFFormula (Formula)

data Semicircuit
  = Semicircuit
      IndicatorFunctionCalls
      FunctionCalls
      Formula

newtype IndicatorFunctionCalls
  = IndicatorFunctionCalls (Set IndicatorFunctionCall)

newtype FunctionCalls
  = FunctionCalls (Set FunctionCall)

data IndicatorFunctionCall
  = IndicatorFunctionCall Term Term

data FunctionCall
  = FunctionCall Name (NonEmpty Term)
