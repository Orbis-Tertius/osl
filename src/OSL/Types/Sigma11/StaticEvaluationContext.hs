{-# LANGUAGE DeriveGeneric #-}

module OSL.Types.Sigma11.StaticEvaluationContext (StaticEvaluationContextF (StaticEvaluationContext)) where

import Data.Map (Map)
import GHC.Generics (Generic)
import OSL.Types.Sigma11 (OutputBoundF)

newtype StaticEvaluationContextF name =
  StaticEvaluationContext
    { unStaticEvaluationContext ::
        Map name (OutputBoundF name)
    }
  deriving Generic
