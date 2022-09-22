module OSL.EntryPoint (main, runMain) where


import Control.Monad.Trans.State.Strict (runStateT)
import Data.Text (pack)
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


main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName, targetName] -> putStrLn =<< runMain fileName targetName
    _ -> putStrLn "Error: please provide a filename and the name of a term and nothing else"


runMain :: String -> String -> IO String
runMain fileName targetName = do
  source <- readFile fileName
  case tokenize fileName source of
    Left err -> pure $ "Tokenizing error: " <> show err
    Right toks -> do
      case parseContext fileName toks of
        Left err -> pure $ "Parse error: " <> show err
        Right rawCtx -> do
          case validateContext rawCtx of
            Left err -> pure $ "Type checking error: " <> show err
            Right validCtx ->
              case buildTranslationContext validCtx of
                Right gc -> do
                  let lc = toLocalTranslationContext gc
                  case getDeclaration validCtx (Sym (pack targetName)) of
                    Just (Defined _ targetTerm) ->
                      case runStateT (translateToFormula gc lc targetTerm) mempty of
                        Left err -> pure $ "Error translating: " <> show err
                        Right (translated, aux) ->
                          pure $ "Translated OSL:\n" <> show translated <>
                            (if aux == mempty then "" else "\n\nAux Data:\n" <> show aux)
                    _ -> pure "please provide the name of a defined term"
                Left err -> pure $ "Error building context: " <> show err
