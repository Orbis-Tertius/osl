{-# LANGUAGE DataKinds #-}

module OSL.Spec.SudokuSpec (spec) where

import Data.Text (pack)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Types.OSL (ValidContext, ContextType (Global))
import OSL.ValidateContext (validateContext)
import Test.Syd (Spec, describe, liftIO, expectationFailure)
import Text.Parsec (SourcePos)

spec :: Spec
spec =
  describe "Sudoku" $ do
    let sudokuSpecFile = "examples/sudoku.osl"
    sudokuSpecTxt <- pack <$> liftIO (readFile sudokuSpecFile)
    case tokenize sudokuSpecFile sudokuSpecTxt of
      Right toks ->
        case parseContext sudokuSpecFile toks of
          Right rawCtx ->
            case validateContext rawCtx of
              Right validCtx ->
                spec' validCtx
              Left err -> liftIO . expectationFailure $
                "invalid context: " <> show err
          Left err -> liftIO . expectationFailure $
            "parse error: " <> show err
      Left err -> liftIO . expectationFailure $
        "tokenizing error: " <> show err

spec' :: ValidContext 'Global SourcePos -> Spec
spec' = todo

todo :: a
todo = todo
