{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}

module OSL.Satisfaction (satisfies, satisfiesSimple) where

import Control.Lens ((^.))
import qualified Data.Map as Map
import Data.Tuple.Extra (curry3)
import OSL.Evaluation (evaluate)
import OSL.Types.Argument (Argument (Argument), Statement (Statement))
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.OSL (ContextType (Global, Local), Declaration (FreeVariable), Term (Lambda), Type (F), ValidContext (ValidContext))
import OSL.Types.Value (Value (Bool, Pair'))
import OSL.ValidateContext (inferType)
import OSL.Witness (preprocessWitness)

satisfiesSimple :: (Ord ann, Show ann) => ValidContext 'Global ann -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfiesSimple c x arg = do
  xT <- inferType c x
  satisfies c (ValidContext (c ^. #unValidContext)) mempty xT x arg

satisfies :: (Ord ann, Show ann) => ValidContext 'Global ann -> ValidContext 'Local ann -> EvaluationContext -> Type ann -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfies gc lc e = curry3 $
  \case
    ( F _ann _n a b,
      Lambda _ann' v _a' body,
      Argument (Statement (Pair' vs s')) w
      ) ->
        satisfies
          gc
          (lc <> ValidContext (Map.singleton v (FreeVariable a)))
          (e <> EvaluationContext (Map.singleton v vs))
          b
          body
          (Argument (Statement s') w)
    (a, x, Argument _ w) -> do
      pw <- preprocessWitness x w
      (== Bool True) <$> evaluate gc pw lc a x e
