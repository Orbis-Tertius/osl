{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Sigma11.EvaluationContext (EvaluationContextF (EvaluationContext), EvaluationContext) where

import Data.Map (Map)
import GHC.Generics (Generic)
import OSL.Types.Sigma11 (Name, PredicateName)
import OSL.Types.Sigma11.Value (Value)

newtype EvaluationContextF name = EvaluationContext
  {unEvaluationContext :: Map (Either name PredicateName) Value}
  deriving (Semigroup, Monoid, Generic, Show)

type EvaluationContext = EvaluationContextF Name
