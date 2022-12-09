{-# LANGUAGE DeriveGeneric #-}

module OSL.Types.PreprocessedWitness (PreprocessedWitness (PreprocessedWitness)) where

import GHC.Generics (Generic)
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.EvaluationContext (EvaluationContext)
import OSL.Types.Value (Value)

-- Given the annotation of an existential quantifier
-- and an evaluation context, return the applicable
-- witness (if any).
newtype PreprocessedWitness ann = PreprocessedWitness
  { unPreprocessedWitness ::
      ann ->
      EvaluationContext ->
      Either (ErrorMessage ann) Value
  }
  deriving (Generic)
