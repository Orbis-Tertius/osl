module Semicircuit.Types.Semicircuit
  ( Semicircuit (..)
  , IndicatorFunctionCalls (..)
  , FunctionCalls (..)
  ) where


data Semicircuit =
  Semicircuit
  IndicatorFunctionCalls
  FunctionCalls
  PNFFormula'


newtype IndicatorFunctionCalls =
  IndicatorFunctionCalls (Set IndicatorFunctionCall)


newtype FunctionCalls =
  FunctionCalls (Set FunctionCall)


data IndicatorFunctionCall =
  IndicatorFunctionCall
  Term
  Term


data FunctionCall =
  FunctionCall
  Name
  (NonEmpty Term)
