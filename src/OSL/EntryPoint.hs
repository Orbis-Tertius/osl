{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.EntryPoint
  ( main,
    runMain,
    FileName (..),
    TargetName (..),
    Output (..),
    CompileToCircuit (CompileToCircuit, DONTCompileToCircuit),
  )
where

import Control.Monad.Trans.State.Strict (runStateT)
import Data.ByteString (readFile)
import Data.Either.Extra (mapLeft)
import Data.Text (Text, pack)
import Data.Text.Encoding (decodeUtf8')
import Halo2.CircuitMetrics (getCircuitMetrics)
import Halo2.Types.BitsPerByte (BitsPerByte (BitsPerByte))
import Halo2.Types.RowCount (RowCount (RowCount))
import OSL.ActusDictionary (actusDictionaryFormatted)
import OSL.BuildTranslationContext (buildTranslationContext)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Translate (translateToFormula)
import OSL.TranslationContext (toLocalTranslationContext)
import OSL.Types.FileName (FileName (FileName))
import OSL.Types.OSL (Declaration (Defined), Name (Sym))
import OSL.ValidContext (getDeclaration)
import OSL.ValidateContext (validateContext)
import Semicircuit.Gensyms (deBruijnToGensyms)
import Semicircuit.PNFFormula (toPNFFormula, toSemicircuit)
import Semicircuit.PrenexNormalForm (toPrenexNormalForm, toStrongPrenexNormalForm)
import Semicircuit.Sigma11 (prependQuantifiers)
import Semicircuit.ToLogicCircuit (semicircuitToLogicCircuit)
import System.Environment (getArgs)
import Trace.FromLogicCircuit (getMapping, logicCircuitToTraceType)
import Trace.Metrics (getTraceTypeMetrics)
import Trace.ToArithmeticAIR (mappings)
import Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit)
import Prelude hiding (readFile)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["actus-dictionary"] ->
      putStrLn . unOutput
        =<< genActusDictionary
    [fileName, targetName] ->
      putStrLn . unOutput
        =<< runMain (FileName fileName) (TargetName targetName) CompileToCircuit
    [fileName, targetName, "--test"] ->
      putStrLn . unOutput
        =<< runMain (FileName fileName) (TargetName targetName) DONTCompileToCircuit
    _ -> putStrLn "Usage: osl FILE TARGET [--test]"

newtype TargetName = TargetName String

newtype ErrorMessage = ErrorMessage String

newtype SuccessfulOutput = SuccessfulOutput String

newtype Source = Source Text

newtype Output = Output {unOutput :: String}
  deriving newtype (Eq, Show)

runMain :: FileName -> TargetName -> CompileToCircuit -> IO Output
runMain (FileName fileName) (TargetName targetName) compileToCircuit = do
  sourceBs <- readFile fileName
  case decodeUtf8' sourceBs of
    Right source ->
      case calcMain
        (FileName fileName)
        (TargetName targetName)
        (Source source) -- TODO: specify BitsPerByte and RowCount with options
        (BitsPerByte 8)
        (RowCount 81)
        compileToCircuit of
        Left (ErrorMessage err) -> pure (Output err)
        Right (SuccessfulOutput result) -> pure (Output result)
    _ -> pure (Output "could not decode source file; is it not UTF-8?")

data CompileToCircuit
  = CompileToCircuit
  | DONTCompileToCircuit

calcMain ::
  FileName ->
  TargetName ->
  Source ->
  BitsPerByte ->
  RowCount ->
  CompileToCircuit ->
  Either ErrorMessage SuccessfulOutput
calcMain (FileName fileName) (TargetName targetName) (Source source) bitsPerByte rowCount compileToCircuit = do
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
      let translatedOutput =
            "Translated OSL:\n"
              <> show translated
              <> (if aux == mempty then "" else "\n\nAux Data:\n" <> show aux)
      case compileToCircuit of
        DONTCompileToCircuit ->
          pure (SuccessfulOutput translatedOutput)
        CompileToCircuit -> do
          pnf <-
            mapLeft (ErrorMessage . ("Error converting to prenex normal form: " <>) . show) $
              toPrenexNormalForm () (fst (deBruijnToGensyms translated))
          spnf <-
            mapLeft (ErrorMessage . ("Error converting to strong prenex normal form: " <>) . show) $
              uncurry (toStrongPrenexNormalForm ()) pnf
          -- let sspnf = uncurry toSuperStrongPrenexNormalForm spnf
          pnff <-
            mapLeft (ErrorMessage . ("Error converting to PNF formula: " <>) . show) $
              toPNFFormula () (uncurry prependQuantifiers spnf)
          let semi = toSemicircuit pnff
              (logic, layout) = semicircuitToLogicCircuit rowCount semi
              traceLayout = getMapping 8 logic
              traceType = logicCircuitToTraceType bitsPerByte logic
              circuitLayout = mappings traceType traceLayout
              circuit = traceTypeToArithmeticCircuit traceType traceLayout
              circuitMetrics = getCircuitMetrics circuit
              traceTypeMetrics = getTraceTypeMetrics traceType
          pure . SuccessfulOutput $
            translatedOutput
              <> "\n\nTrace type metrics: "
              <> show traceTypeMetrics
              <> "\n\nCircuit metrics: "
              <> show circuitMetrics
              <> "\n\nPrenex normal form: "
              <> show pnf
              <> "\n\nStrong prenex normal form: "
              <> show spnf
              -- <> "\n\nSuper strong prenex normal form: "
              -- <> show sspnf
              <> "\n\nPNF formula: "
              <> show pnff
              <> "\n\nSemicircuit: "
              <> show semi
              <> "\n\nLayout: "
              <> show layout
              <> "\n\nLogic circuit: "
              <> show logic
              <> "\n\nTrace type layout: "
              <> show traceLayout
              <> "\n\nTrace type: "
              <> show traceType
              <> "\n\nArithmetic circuit layout:\n"
              <> show circuitLayout
              <> "\n\nArithmetic circuit:\n"
              <> show circuit
    _ -> Left . ErrorMessage $ "please provide the name of a defined term"

genActusDictionary :: IO Output
genActusDictionary =
  pure $ Output actusDictionaryFormatted
