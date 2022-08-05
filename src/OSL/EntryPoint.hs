module OSL.EntryPoint (main) where


import Data.Text.IO (readFile)
import Prelude hiding (readFile)
import System.Environment (getArgs)

import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.ValidateContext (validateContext)


main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName] -> do
      source <- readFile fileName
      case tokenize fileName source of
        Left err -> putStrLn $ "Tokenizing error: " <> show err
        Right toks -> do
          case parseContext fileName toks of
            Left err -> putStrLn $ "Parse error: " <> show err
            Right rawCtx -> do
              case validateContext rawCtx of
                Left err -> putStrLn $ "Type checking error: " <> show err
                Right _ -> putStrLn "Validated OSL"
    _ -> putStrLn "Error: please provide a filename and nothing else"
