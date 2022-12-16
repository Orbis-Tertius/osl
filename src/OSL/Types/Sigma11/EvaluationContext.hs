{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Sigma11.EvaluationContext (EvaluationContext (EvaluationContext)) where

import GHC.Generics (Generic)
import Data.Map (Map)
import OSL.Types.Sigma11 (Name, PredicateName)
import OSL.Types.Sigma11.Value (Value)

newtype EvaluationContext =
  EvaluationContext
    { unEvaluationContext :: Map (Either Name PredicateName) Value }
  deriving (Semigroup, Monoid, Generic)
