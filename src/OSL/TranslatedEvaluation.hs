{-# LANGUAGE OverloadedStrings #-}

module OSL.TranslatedEvaluation
  ( evalTranslatedFormula1,
    evalTranslatedFormula2,
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
import Semicircuit.Gensyms (deBruijnToGensyms, deBruijnToGensymsEvalContext)

-- First codegen pass: OSL -> Sigma11
evalTranslatedFormula1 ::
  Show ann =>
  ValidContext t ann ->
  Name ->
  ArgumentForm ->
  Argument ->
  Either (ErrorMessage (Maybe ann)) Bool
evalTranslatedFormula1 c name argumentForm argument = do
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

-- Second codegen pass: OSL.Sigma11 -> Semicircuit.Sigma11
-- (replaces de Bruijn indices with gensyms)
evalTranslatedFormula2 ::
  Show ann =>
  ValidContext t ann ->
  Name ->
  ArgumentForm ->
  Argument ->
  Either (ErrorMessage (Maybe ann)) Bool
evalTranslatedFormula2 c name argumentForm argument = do
  (def, translated, aux) <- translateToFormulaSimple c name
  let (translated', mapping) = deBruijnToGensyms translated
  ec <-
    mapLeft
      (\(ErrorMessage () msg) -> ErrorMessage Nothing ("auxTablesToEvalContext: " <> msg))
      (S11.auxTablesToEvalContext aux)
  let ec' = deBruijnToGensymsEvalContext mapping ec
  s11arg <-
    mapLeft
      (\(ErrorMessage () msg) -> ErrorMessage Nothing ("toSigma11Argument: " <> msg))
      (toSigma11Argument c argumentForm argument (dropTermAnnotations def))
  mapLeft
    (\(ErrorMessage () msg) -> ErrorMessage Nothing ("evalFormula: " <> msg))
    (S11.evalFormula ec' s11arg translated')
