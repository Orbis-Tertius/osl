{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.EntryPoint
  ( main,
    runMain,
    FileName (..),
    TargetName (..),
    Output (..),
  )
where

import Control.Monad.Trans.State.Strict (runStateT)
import Data.ByteString (readFile)
import Data.Either.Extra (mapLeft)
import Data.Text (Text, pack)
import Data.Text.Encoding (decodeUtf8')
import OSL.BuildTranslationContext (buildTranslationContext)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Translate (translateToFormula)
import OSL.TranslationContext (toLocalTranslationContext)
import OSL.Types.OSL (Declaration (Defined), Name (Sym))
import OSL.ValidContext (getDeclaration)
import OSL.ValidateContext (validateContext)
import Semicircuit.Gensyms (deBruijnToGensyms)
import Semicircuit.PNFFormula (toPNFFormula)
import Semicircuit.PrenexNormalForm (toPrenexNormalForm, toStrongPrenexNormalForm)
import Semicircuit.Sigma11 (prependQuantifiers)
import System.Environment (getArgs)
import Prelude hiding (readFile)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName, targetName] ->
      putStrLn . unOutput
        =<< runMain (FileName fileName) (TargetName targetName)
    _ -> putStrLn "Error: please provide a filename and the name of a term and nothing else"

newtype FileName = FileName String

newtype TargetName = TargetName String

newtype ErrorMessage = ErrorMessage String

newtype SuccessfulOutput = SuccessfulOutput String

newtype Source = Source Text

newtype Output = Output {unOutput :: String}
  deriving newtype (Eq, Show)

runMain :: FileName -> TargetName -> IO Output
runMain (FileName fileName) (TargetName targetName) = do
  sourceBs <- readFile fileName
  case decodeUtf8' sourceBs of
    Right source ->
      case calcMain (FileName fileName) (TargetName targetName) (Source source) of
        Left (ErrorMessage err) -> pure (Output err)
        Right (SuccessfulOutput result) -> pure (Output result)
    _ -> pure (Output "could not decode source file; is it not UTF-8?")

calcMain :: FileName -> TargetName -> Source -> Either ErrorMessage SuccessfulOutput
calcMain (FileName fileName) (TargetName targetName) (Source source) = do
  toks <-
    mapLeft (ErrorMessage . ("Tokenizing error: " <>) . show) $
      tokenize fileName source
  rawCtx <-
    mapLeft (ErrorMessage . ("Parse error: " <>) . show) $
      parseContext fileName toks
  validCtx <-
    mapLeft (ErrorMessage . ("Type checking error: " <>) . show) $
      validateContext rawCtx
  gc <-
    mapLeft (ErrorMessage . ("Error building context: " <>) . show) $
      buildTranslationContext validCtx
  let lc = toLocalTranslationContext gc
  case getDeclaration validCtx (Sym (pack targetName)) of
    Just (Defined _ targetTerm) -> do
      (translated, aux) <-
        mapLeft (ErrorMessage . ("Error translating: " <>) . show) $
          runStateT (translateToFormula gc lc targetTerm) mempty
      pnf <-
        mapLeft (ErrorMessage . ("Error converting to prenex normal form: " <>) . show) $
          toPrenexNormalForm () (deBruijnToGensyms translated)
      spnf <-
        mapLeft (ErrorMessage . ("Error converting to strong prenex normal form: " <>) . show) $
          uncurry (toStrongPrenexNormalForm ()) pnf
      _ <-
        mapLeft (ErrorMessage . ("Error converting to PNF formula: " <>) . show) $
          toPNFFormula () (uncurry prependQuantifiers spnf)
      pure . SuccessfulOutput $
        "Translated OSL:\n"
          <> show translated
          <> (if aux == mempty then "" else "\n\nAux Data:\n" <> show aux)
    _ -> Left . ErrorMessage $ "please provide the name of a defined term"
