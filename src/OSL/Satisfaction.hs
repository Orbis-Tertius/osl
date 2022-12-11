{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module OSL.Satisfaction (satisfies) where

import qualified Data.Map as Map
import OSL.Types.Argument (Argument (Argument), Statement (Statement))
import OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (ContextType (Global), Term (Lambda), ValidContext)
import OSL.Types.Value (Value (Pair'))

satisfies :: ValidContext 'Global ann -> EvaluationContext -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfies c e = curry $
  \case
    (Lambda _ann v _b body, Argument (Statement (Pair' vs s')) w) ->
      satisfies
        c
        (e <> EvaluationContext (Map.singleton v vs))
        body
        (Argument (Statement s') w)

todo :: a
todo = todo
