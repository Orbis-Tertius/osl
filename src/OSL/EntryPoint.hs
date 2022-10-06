{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module OSL.EntryPoint
  ( main
  , runMain
  , FileName (..)
  , TargetName (..)
  , Output (..)
  ) where


import Control.Monad.Trans.State.Strict (runStateT)
import Data.Either.Extra (mapLeft)
import Data.Text (Text, pack)
import Data.Text.IO (readFile)
import Prelude hiding (readFile)
import System.Environment (getArgs)

import OSL.BuildTranslationContext (buildTranslationContext)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Translate (translateToFormula)
import OSL.TranslationContext (toLocalTranslationContext)
import OSL.Types.OSL (Declaration (Defined), Name (Sym))
import OSL.ValidateContext (validateContext)
import OSL.ValidContext (getDeclaration)
import Semicircuit.Gensyms (deBruijnToGensyms)
import Semicircuit.PNFFormula (toPNFFormula)
import Semicircuit.PrenexNormalForm (toStrongPrenexNormalForm, toPrenexNormalForm)
import Semicircuit.Sigma11 (prependQuantifiers)


main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName, targetName] -> putStrLn . unOutput
      =<< runMain (FileName fileName) (TargetName targetName)
    _ -> putStrLn "Error: please provide a filename and the name of a term and nothing else"


newtype FileName = FileName String


newtype TargetName = TargetName String


newtype ErrorMessage = ErrorMessage String


newtype SuccessfulOutput = SuccessfulOutput String


newtype Source = Source Text


newtype Output = Output { unOutput :: String }
  deriving newtype (Eq, Show)


runMain :: FileName -> TargetName -> IO Output
runMain (FileName fileName) (TargetName targetName) = do
  source <- readFile fileName
  case calcMain (FileName fileName) (TargetName targetName) (Source source) of
    Left (ErrorMessage err) -> pure (Output err)
    Right (SuccessfulOutput result) -> pure (Output result)


calcMain :: FileName -> TargetName -> Source -> Either ErrorMessage SuccessfulOutput
calcMain (FileName fileName) (TargetName targetName) (Source source) = do
  toks <- mapLeft (ErrorMessage . ("Tokenizing error: " <>) . show)
          $ tokenize fileName source
  rawCtx <- mapLeft (ErrorMessage . ("Parse error: " <>) . show)
            $ parseContext fileName toks
  validCtx <- mapLeft (ErrorMessage . ("Type checking error: " <>) . show)
              $ validateContext rawCtx
  gc <- mapLeft (ErrorMessage . ("Error building context: " <>) . show)
        $ buildTranslationContext validCtx
  let lc = toLocalTranslationContext gc
  case getDeclaration validCtx (Sym (pack targetName)) of
    Just (Defined _ targetTerm) -> do
      (translated, aux) <-
        mapLeft (ErrorMessage . ("Error translating: " <>) . show)
        $ runStateT (translateToFormula gc lc targetTerm) mempty
      pnf <- mapLeft (ErrorMessage . ("Error converting to prenex normal form: " <>) . show)
             $ toPrenexNormalForm () (deBruijnToGensyms translated)
      spnf <- mapLeft (ErrorMessage . ("Error converting to strong prenex normal form: " <>) . show)
          $ uncurry (toStrongPrenexNormalForm ()) pnf
      _ <- mapLeft (ErrorMessage . ("Error converting to PNF formula: " <>) . show)
           $ toPNFFormula () (uncurry prependQuantifiers spnf)
      pure . SuccessfulOutput $ "Translated OSL:\n"
        <> show translated <>
        (if aux == mempty then "" else "\n\nAux Data:\n" <> show aux)
    _ -> Left . ErrorMessage $ "please provide the name of a defined term"
