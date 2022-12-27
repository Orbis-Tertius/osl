{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Sigma11.EvaluationContext (EvaluationContext (EvaluationContext)) where

import Data.Map (Map)
import GHC.Generics (Generic)
import OSL.Types.Sigma11 (Name, PredicateName)
import OSL.Types.Sigma11.Value (Value)

newtype EvaluationContext = EvaluationContext
  {unEvaluationContext :: Map (Either Name PredicateName) Value}
  deriving (Semigroup, Monoid, Generic, Show)
