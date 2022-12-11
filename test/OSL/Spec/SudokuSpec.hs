{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Spec.SudokuSpec (spec) where

import Control.Lens ((^.))
import qualified Data.Map as Map
import Data.Text (pack)
import OSL.ArgumentForm (getArgumentForm)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Types.ArgumentForm (ArgumentForm (ArgumentForm))
import OSL.Types.OSL (ValidContext, ContextType (Global), Declaration (Defined), Name (Sym))
import OSL.ValidateContext (validateContext)
import Test.Syd (Spec, describe, liftIO, expectationFailure, it, shouldBe)
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
spec' c = do
  argumentFormSpec c

argumentFormSpec :: ValidContext 'Global SourcePos -> Spec
argumentFormSpec c =
  it "has the correct argument form" $
    case Map.lookup (Sym "problemIsSolvable")
           (c ^. #unValidContext) of
      Just (Defined t x) ->
        getArgumentForm c t x `shouldBe`
          Right (ArgumentForm mempty mempty)
      _ ->
        liftIO . expectationFailure $
          "problemIsSolvable definition not found"
