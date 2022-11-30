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

-- import Control.Lens ((^.))
import Control.Monad.Trans.State.Strict (runStateT)
import Data.ByteString (readFile)
import Data.Either.Extra (mapLeft)
import Data.Text (Text, pack)
import Data.Text.Encoding (decodeUtf8')
import Halo2.CircuitMetrics (getCircuitMetrics)
import Halo2.Types.BitsPerByte (BitsPerByte (BitsPerByte))
import Halo2.Types.RowCount (RowCount (RowCount))
import OSL.BuildTranslationContext (buildTranslationContext)
import OSL.Parse (parseContext)
import OSL.Tokenize (tokenize)
import OSL.Translate (translateToFormula)
import OSL.TranslationContext (toLocalTranslationContext)
import OSL.Types.OSL (Declaration (Defined), Name (Sym))
import OSL.ValidContext (getDeclaration)
import OSL.ValidateContext (validateContext)
-- import Semicircuit.DNFFormula (fromDisjunctiveNormalForm, toDisjunctiveNormalForm)
import Semicircuit.Gensyms (deBruijnToGensyms)
import Semicircuit.PNFFormula (toPNFFormula, toSemicircuit)
import Semicircuit.PrenexNormalForm (toPrenexNormalForm, toStrongPrenexNormalForm)
import Semicircuit.Sigma11 (prependQuantifiers)
-- import qualified Semicircuit.Types.PNFFormula as PNF
import Semicircuit.ToLogicCircuit (semicircuitToLogicCircuit)
import System.Environment (getArgs)
import Trace.FromLogicCircuit (logicCircuitToTraceType)
import Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit)
import Prelude hiding (readFile)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName, targetName] ->
      putStrLn . unOutput
        =<< runMain (FileName fileName) (TargetName targetName) CompileToCircuit
    [fileName, targetName, "--test"] ->
      putStrLn . unOutput
        =<< runMain (FileName fileName) (TargetName targetName) DONTCompileToCircuit
    _ -> putStrLn "Usage: osl FILE TARGET [--test]"

newtype FileName = FileName String

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
        (RowCount 8)
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
      pnf <-
        mapLeft (ErrorMessage . ("Error converting to prenex normal form: " <>) . show) $
          toPrenexNormalForm () (deBruijnToGensyms translated)
      spnf <-
        mapLeft (ErrorMessage . ("Error converting to strong prenex normal form: " <>) . show) $
          uncurry (toStrongPrenexNormalForm ()) pnf
      pnff <-
        mapLeft (ErrorMessage . ("Error converting to PNF formula: " <>) . show) $
          toPNFFormula () (uncurry prependQuantifiers spnf)
      let -- dnf = fromDisjunctiveNormalForm (toDisjunctiveNormalForm (pnff ^. #qfFormula))
          semi = toSemicircuit pnff -- (PNF.Formula dnf (pnff ^. #quantifiers))
          (logic, layout) = semicircuitToLogicCircuit rowCount semi
          traceType = logicCircuitToTraceType bitsPerByte logic
          circuit = traceTypeToArithmeticCircuit traceType
          metrics = getCircuitMetrics circuit
      pure . SuccessfulOutput $
        "Translated OSL:\n"
          <> show translated
          <> (if aux == mempty then "" else "\n\nAux Data:\n" <> show aux)
          <> ( case compileToCircuit of
                 CompileToCircuit ->
                   "\n\nMetrics: "
                     <> show metrics
                     <> "\n\nPrenex normal form: "
                     <> show pnf
                     <> "\n\nStrong prenex normal form: "
                     <> show spnf
                     <> "\n\nPNF formula: "
                     <> show pnff
                     <> "\n\nSemicircuit: "
                     <> show semi
                     <> "\n\nLayout: "
                     <> show layout
                     <> "\n\nLogic circuit: "
                     <> show logic
                     <> "\n\nTrace type: "
                     <> show traceType
                     <> "\n\nArithmetic circuit:\n"
                     <> show circuit
                 DONTCompileToCircuit ->
                   mempty
             )
    _ -> Left . ErrorMessage $ "please provide the name of a defined term"
