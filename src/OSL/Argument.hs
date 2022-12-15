module OSL.Argument (toSigma11Argument) where

import OSL.Types.ErrorMessage (ErrorMessage)
import qualified OSL.Types.ArgumentForm as OSL
import qualified OSL.Types.Argument as OSL
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Value as OSL
import qualified OSL.Types.Sigma11.Argument as S11
import qualified OSL.Types.Sigma11.Value as S11

toSigma11Argument ::
  OSL.ArgumentForm ->
  OSL.Argument ->
  Either (ErrorMessage ()) S11.Argument
toSigma11Argument = todo

todo :: a
todo = todo
