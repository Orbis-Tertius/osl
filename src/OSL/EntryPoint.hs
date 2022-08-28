module OSL.EntryPoint (main) where


import Data.Text (pack)
import Data.Text.IO (readFile)
import Prelude hiding (readFile)
import System.Environment (getArgs)

import OSL.BuildTranslationContext (buildTranslationContext)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Translate (translateToFormula)
import OSL.Types.OSL (Declaration (Defined), Name (Sym))
import OSL.ValidateContext (validateContext)
import OSL.ValidContext (getDeclaration)


main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName, targetName] -> do
      source <- readFile fileName
      case tokenize fileName source of
        Left err -> putStrLn $ "Tokenizing error: " <> show err
        Right toks -> do
          case parseContext fileName toks of
            Left err -> putStrLn $ "Parse error: " <> show err
            Right rawCtx -> do
              case validateContext rawCtx of
                Left err -> putStrLn $ "Type checking error: " <> show err
                Right validCtx ->
                  case buildTranslationContext validCtx of
                    Right transCtx -> do
                      case getDeclaration validCtx (Sym (pack targetName)) of
                        Just (Defined _ targetTerm) ->
                          case translateToFormula transCtx targetTerm of
                            Left err -> putStrLn $ "Error translating: " <> show err
                            Right translated -> putStrLn $ "Translated OSL:\n" <> show translated
                        _ -> putStrLn "please provide the name of a defined term"
                    Left err -> putStrLn $ "Error building context: " <> show err
    _ -> putStrLn "Error: please provide a filename and the name of a term and nothing else"
