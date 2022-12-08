{-# LANGUAGE DeriveGeneric #-}

module OSL.Types.PreprocessedWitness (PreprocessedWitness (PreprocessedWitness)) where

import GHC.Generics (Generic)
import Data.Map (Map)
import OSL.Types.EvaluationContext (EvaluationContext)
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.Value (Value)

newtype PreprocessedWitness ann =
  PreprocessedWitness
  { unPreprocessedWitness ::
      Map ann (EvaluationContext -> Either (ErrorMessage ann) Value)
  }
  deriving Generic
