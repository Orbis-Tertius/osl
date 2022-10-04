module OSL.EntryPoint (main, runMain) where


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
import Semicircuit.PNFFormula (toPNFFormula)


main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName, targetName] -> putStrLn =<< runMain fileName targetName
    _ -> putStrLn "Error: please provide a filename and the name of a term and nothing else"


runMain :: String -> String -> IO String
runMain fileName targetName = do
  source <- readFile fileName
  case calcMain fileName targetName source of
    Left err -> pure err
    Right result -> pure result


calcMain :: String -> String -> Text -> Either String String
calcMain fileName targetName source = do
  toks <- mapLeft (("Tokenizing error: " <>) . show)
          $ tokenize fileName source
  rawCtx <- mapLeft (("Parse error: " <>) . show)
            $ parseContext fileName toks
  validCtx <- mapLeft (("Type checking error: " <>) . show)
              $ validateContext rawCtx
  gc <- mapLeft (("Error building context: " <>) . show)
        $ buildTranslationContext validCtx
  let lc = toLocalTranslationContext gc
  case getDeclaration validCtx (Sym (pack targetName)) of
    Just (Defined _ targetTerm) -> do
      (translated, aux) <-
        mapLeft (("Error translating: " <>) . show)
        $ runStateT (translateToFormula gc lc targetTerm) mempty
      _ <- mapLeft (("Error converting to PNF formula: " <>) . show)
           $ toPNFFormula () translated
      pure $ "Translated OSL:\n" <> show translated <>
        (if aux == mempty then "" else "\n\nAux Data:\n" <> show aux)
    _ -> pure "please provide the name of a defined term"
