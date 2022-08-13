module OSL.Translate
  ( translate
  ) where


import OSL.Types.OSL (ValidContext)
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11


translate
  :: ValidContext
  -> TranslationContext
  -> OSL.Name
  -> Either ErrorMessage S11.Formula
translate = todo


todo :: a
todo = todo
