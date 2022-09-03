module OSL.Types.Translation (Translation (..)) where


import OSL.Types.Sigma11 (Formula, Term)
import OSL.Types.TranslationContext (Mapping)


data Translation ann =
    Formula Formula
  | Term Term
  | Mapping (Mapping ann Term)
