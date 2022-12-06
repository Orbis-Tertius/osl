{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext)) where

import GHC.Generics (Generic)
import Data.Map (Map, toList)
import OSL.Types.OSL (Name)
import OSL.Types.Value (Value)

newtype EvaluationContext =
  EvaluationContext
  { unEvaluationContext ::
    Map Name Value
  }
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Semigroup, Monoid)

instance Show EvaluationContext where
  show = show . toList . unEvaluationContext
