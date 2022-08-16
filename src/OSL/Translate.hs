module OSL.Translate
  ( translate
  ) where


import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (ValidContext)
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.TranslationContext (TranslationContext)


translate
  :: ValidContext ann
  -> TranslationContext ann
  -> OSL.Name
  -> Either (ErrorMessage ann) S11.Formula
translate = todo


todo :: a
todo = todo
