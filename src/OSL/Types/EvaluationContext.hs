{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext)) where

import Data.Map (Map)
import GHC.Generics (Generic)
import OSL.Types.OSL (Name)
import OSL.Types.PreValue (PreValue)

newtype EvaluationContext ann = EvaluationContext
  { unEvaluationContext ::
      Map Name (PreValue ann)
  }
  deriving stock (Generic)
  deriving newtype (Semigroup, Monoid)
