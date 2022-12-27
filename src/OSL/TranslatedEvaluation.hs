{-# LANGUAGE OverloadedStrings #-}

module OSL.TranslatedEvaluation
  ( evalTranslatedFormula,
  )
where

import Data.Either.Extra (mapLeft)
import OSL.Argument (toSigma11Argument)
import qualified OSL.Sigma11 as S11
import OSL.Term (dropTermAnnotations)
import OSL.Translate (translateToFormulaSimple)
import OSL.Types.Argument (Argument)
import OSL.Types.ArgumentForm (ArgumentForm)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.OSL (Name, ValidContext)

evalTranslatedFormula ::
  Show ann =>
  ValidContext t ann ->
  Name ->
  ArgumentForm ->
  Argument ->
  Either (ErrorMessage (Maybe ann)) Bool
evalTranslatedFormula c name argumentForm argument = do
  (def, translated, aux) <- translateToFormulaSimple c name
  ec <-
    mapLeft
      (\(ErrorMessage () msg) -> ErrorMessage Nothing ("auxTablesToEvalContext: " <> msg))
      (S11.auxTablesToEvalContext aux)
  s11arg <-
    mapLeft
      (\(ErrorMessage () msg) -> ErrorMessage Nothing ("toSigma11Argument: " <> msg))
      (toSigma11Argument c argumentForm argument (dropTermAnnotations def))
  mapLeft
    (\(ErrorMessage () msg) -> ErrorMessage Nothing ("evalFormula: " <> msg))
    (S11.evalFormula ec s11arg translated)
