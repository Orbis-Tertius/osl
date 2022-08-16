module OSL.Types.Translation (Translation (..)) where


import OSL.Types.Sigma11 (Formula, Term)
import OSL.Types.TranslationContext (Mapping)


data Translation =
    Formula Formula
  | Term Term
  | Mapping Mapping
