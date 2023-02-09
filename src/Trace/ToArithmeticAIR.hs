{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Trace.ToArithmeticAIR
  ( traceTypeToArithmeticAIR,
    Mapping (Mapping),
    CaseNumber,
    Mappings (Mappings),
    FixedMappings (FixedMappings),
    mappings,
    traceToArgument,
  )
where

import Cast (intToInteger, integerToInt)
import Control.Arrow (second)
import Control.Lens ((<&>))
import Data.List.Extra (mconcatMap, (!?))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (pack)
import Die (die)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import Halo2.Types.AIR (AIR (AIR), ArithmeticAIR)
import Halo2.Types.Argument (Argument (Argument), Statement (Statement), Witness (Witness))
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Advice, Fixed, Instance))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.FixedColumn (FixedColumn (FixedColumn))
import Halo2.Types.FixedValues (FixedValues (FixedValues))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (PolynomialConstraints))
import Halo2.Types.RowIndex (RowIndex (RowIndex), RowIndexType (Absolute))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Stark.Types.Scalar (Scalar, integerToScalar, scalarToInt, zero, one, scalarToInteger)
import Trace.FromLogicCircuit (getDefaultAdvice)
import qualified Trace.FromLogicCircuit as LC
import Trace.Types (InputSubexpressionId (InputSubexpressionId), OutputSubexpressionId (OutputSubexpressionId), ResultExpressionId, StepType, StepTypeId, SubexpressionId (SubexpressionId), SubexpressionLink (SubexpressionLink), TraceType, Trace, Case (Case), SubexpressionTrace (SubexpressionTrace), InputColumnIndex (InputColumnIndex), StepTypeIdSelectionVector)

-- Trace type arithmetic AIRs have the columnar structure
-- of the trace type, with additional fixed columns for:
--  * the table of links, and
--  * the table {(i,1) | i < numCases}.
--
-- Trace type arithmetic AIR gate constraints entail that
-- for each step of each case, the gate constraints of
-- its step type are satisfied.
traceTypeToArithmeticAIR :: TraceType -> LC.Mapping -> ArithmeticAIR
traceTypeToArithmeticAIR t lcM =
  AIR
    (columnTypes t)
    (gateConstraints t)
    (t ^. #rowCount)
    (traceTypeFixedValues t <> additionalFixedValues t (m ^. #fixed))
  where
    m = mappings t lcM

-- Converts the fixed values in the trace type from one per case to
-- one per row.
traceTypeFixedValues ::
  TraceType ->
  FixedValues (RowIndex 'Absolute)
traceTypeFixedValues tt =
  (FixedValues
    (FixedColumn . Map.fromList . zip [0..]
      . concatMap (replicate (Set.size (tt ^. #subexpressions)))
      . Map.elems . (^. #unFixedColumn)
      <$> (tt ^. #fixedValues . #getFixedValues))
     <>)
    . FixedValues
    . fmap f
    . (^. #getFixedValues)
    . mconcat
    . fmap (^. #fixedValues)
    . Map.elems
    $ tt ^. #stepTypes
  where
    f :: FixedColumn Case -> FixedColumn (RowIndex 'Absolute)
    f = FixedColumn
      . Map.fromList
      . zip [0..maxRowIndex tt]
      . concatMap (replicate n)
      . Map.elems
      . (^. #unFixedColumn)

    n = Set.size (tt ^. #subexpressions)

columnTypes :: TraceType -> ColumnTypes
columnTypes t =
  (t ^. #columnTypes)
    <> ColumnTypes
      ( Map.fromList
          ( zip
              [i ..]
              (replicate (4 + n) Fixed)
          )
      )
    <> ColumnTypes
      ( Map.fromList
          (zip [j ..] (replicate (n + 1) Advice))
      )
  where
    i :: ColumnIndex
    i =
      ColumnIndex . length . Map.keys $
        t ^. #columnTypes . #getColumnTypes

    j :: ColumnIndex
    j = ColumnIndex $ (i ^. #getColumnIndex) + 4 + n

    n :: Int
    n = length (t ^. #inputColumnIndices)

gateConstraints :: TraceType -> PolynomialConstraints
gateConstraints t =
  mconcatMap
    (stepTypeGateConstraints (t ^. #stepTypeIdColumnIndices))
    (Map.toList (t ^. #stepTypes))

stepTypeGateConstraints :: StepTypeIdSelectionVector -> (StepTypeId, StepType) -> PolynomialConstraints
stepTypeGateConstraints i (tId, t) =
  PolynomialConstraints
    (second (gateOnStepType i tId) <$> (t ^. #gateConstraints . #constraints))
    -- TODO: degree bound goes up
    (t ^. #gateConstraints . #degreeBound)

gateOnStepType :: StepTypeIdSelectionVector -> StepTypeId -> Polynomial -> Polynomial
gateOnStepType m stId =
  P.times
    $ maybe
        (die "gateOnStepType: step type id column mapping lookup failed")
        P.var'
        (Map.lookup stId (m ^. #unStepTypeIdSelectionVector))

data CaseNumber

data CaseUsed = CaseIsUsed | CaseIsNotUsed
  deriving (Eq)

newtype Mapping a = Mapping {unMapping :: ColumnIndex}
  deriving (Generic, Show)

data Mappings = Mappings
  { fixed :: FixedMappings,
    advice :: AdviceMappings,
    logicCircuit :: LC.Mapping
  }
  deriving (Generic)

data FixedMappings = FixedMappings
  { stepType :: Mapping StepTypeId,
    inputs :: [Mapping InputSubexpressionId],
    output :: Mapping OutputSubexpressionId,
    caseNumber :: Mapping CaseNumber,
    result :: Mapping ResultExpressionId
  }
  deriving (Generic)

data AdviceMappings = AdviceMappings
  { inputs :: [Mapping InputSubexpressionId],
    output :: Mapping OutputSubexpressionId,
    -- The actual number of cases may be less than the maximum
    -- number of cases, so we need to track whether each case
    -- is used or not.
    caseUsed :: Mapping CaseUsed
  }
  deriving (Generic)

newtype AIRFixedValues =
  AIRFixedValues
    { unAIRFixedValues ::
        Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
    }
  deriving (Generic)

getAIRFixedValues ::
  TraceType ->
  Mappings ->
  AIRFixedValues
getAIRFixedValues tt m =
  fixedValuesToAIRFixedValues tt
    (additionalFixedValues tt (m ^. #fixed))

fixedValuesToAIRFixedValues ::
  TraceType ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues
fixedValuesToAIRFixedValues tt fvs =
  AIRFixedValues $
    Map.unionsWith (<>)
      [ Map.singleton ri (Map.singleton ci y)
        | (ci, col) <-
            Map.toList (fvs ^. #getFixedValues),
          (ri, y) <-
            zip [0..n] (padInfinitely (Map.elems (col ^. #unFixedColumn)))
      ]
  where
    n = maxRowIndex tt

maxRowIndex :: TraceType -> RowIndex 'Absolute
maxRowIndex tt =
  RowIndex (c * n - 1)
  where
    c = scalarToInt $ tt ^. #numCases . #unNumberOfCases
    n = Set.size (tt ^. #subexpressions)

mappings :: TraceType -> LC.Mapping -> Mappings
mappings t =
  Mappings
    ( FixedMappings
        (Mapping i :: Mapping StepTypeId)
        (Mapping <$> [j .. k] :: [Mapping InputSubexpressionId])
        (Mapping (k + 1) :: Mapping OutputSubexpressionId)
        (Mapping (k + 2) :: Mapping CaseNumber)
        (Mapping (k + 3) :: Mapping ResultExpressionId)
    )
    ( AdviceMappings
        (Mapping <$> [k + 5 .. l] :: [Mapping InputSubexpressionId])
        (Mapping (l + 1) :: Mapping OutputSubexpressionId)
        (Mapping (l + 2) :: Mapping CaseUsed)
    )
  where
    i :: ColumnIndex
    i = ColumnIndex (Map.size (t ^. #columnTypes . #getColumnTypes))

    j :: ColumnIndex
    j = i + 1

    k :: ColumnIndex
    k = i + ColumnIndex (n-1)

    l :: ColumnIndex
    l = k + 5 + ColumnIndex n

    n :: Int
    n = length (t ^. #inputColumnIndices)

additionalFixedValues ::
  TraceType ->
  FixedMappings ->
  FixedValues (RowIndex 'Absolute)
additionalFixedValues t m =
  linksTableFixedColumns (linksTable t) m
    <> caseAndResultFixedColumns t m

newtype LinksTable = LinksTable
  {unLinksTable :: [SubexpressionLink]}
  deriving (Generic)

linksTable ::
  TraceType ->
  LinksTable
linksTable =
  LinksTable . fmap (\((st, o), is) -> SubexpressionLink st is o) . Map.toList . (^. #links)

linksTableFixedColumns ::
  LinksTable ->
  FixedMappings ->
  FixedValues (RowIndex 'Absolute)
linksTableFixedColumns (LinksTable ls) m =
  FixedValues . Map.fromList $
    [
      ( m ^. #stepType . #unMapping,
        FixedColumn . Map.fromList . zip [0..]
          $ ls <&> (^. #stepType . #unStepTypeId)
      ),
      ( m ^. #output . #unMapping,
        FixedColumn . Map.fromList . zip [0..]
          $ ls <&> (^. #output . #unOutputSubexpressionId . #unSubexpressionId)
      )
    ] <> zip
         ((m ^. #inputs) <&> (^. #unMapping))
         [ FixedColumn . Map.fromList . zip [0..] $
             fromMaybe
               (replicate (length ls) (InputSubexpressionId (SubexpressionId zero)))
               ((ls <&> (^. #inputs)) !? i)
               <&> (^. #unInputSubexpressionId . #unSubexpressionId)
           | i <- [0 .. length (m ^. #inputs) - 1]
         ]

caseAndResultFixedColumns ::
  TraceType ->
  FixedMappings ->
  FixedValues (RowIndex 'Absolute)
caseAndResultFixedColumns t m =
  FixedValues $
    Map.fromList
      [ ( m ^. #caseNumber . #unMapping,
          FixedColumn . Map.fromList . zip [0..] $
            concatMap
              (replicate nResults . f)
              [0 .. nCases - 1]
        ),
        ( m ^. #result . #unMapping,
          FixedColumn . Map.fromList . zip [0..] . concat . replicate nCases $
            f
              <$> [0 .. nResults - 1]
        )
      ]
  where
    nResults = Set.size (t ^. #results)
    nCases = scalarToInt (t ^. #numCases . #unNumberOfCases)

    f :: Int -> Scalar
    f x =
      case integerToScalar (intToInteger x) of
        Just y -> y
        Nothing -> die "caseFixedCoumn: case number out of range of scalar (this is a compiler bug)"

traceToArgument ::
  ann ->
  TraceType ->
  LC.Mapping ->
  Trace ->
  Either (ErrorMessage ann) Argument
traceToArgument ann tt lcM t = do
  mconcat <$> sequence
    [ caseArgument ann tt t m fvs airFvs
        $ maybe
          (die "traceToArgument: case number is out of range of scalar field")
          Case
          (integerToScalar c)
      | c <- [0 .. (scalarToInteger (tt ^. #numCases . #unNumberOfCases)) - 1]
    ]
  where
    m = mappings tt lcM
    air = traceTypeToArithmeticAIR tt lcM
    fvs = air ^. #fixedValues
    airFvs = getAIRFixedValues tt m

caseArgument ::
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues ->
  Case ->
  Either (ErrorMessage ann) Argument
caseArgument ann tt t m fvs airFvs c =
  case Map.lookup c (t ^. #subexpressions) of
    Nothing -> unusedCaseArgument ann tt t m fvs airFvs c
    Just es ->
      if Map.null es
        then unusedCaseArgument ann tt t m fvs airFvs c
        else usedCaseArgument ann tt t m fvs airFvs c es

caseRowIndices ::
  TraceType ->
  Case ->
  [RowIndex 'Absolute]
caseRowIndices tt (Case (scalarToInteger -> c)) =
  [start .. end]
  where
    c' = fromMaybe (die "caseRowIndices: case number out of range of Int")
           (integerToInt c)
    start = RowIndex (n * c')
    end = start + RowIndex n - 1
    -- TODO: n can sometimes be less if we can show that every evaluation will only
    -- require a subset of the subexpressions due to short circuiting, and this would
    -- in turn allow us to decrease the row count
    n = Set.size (tt ^. #subexpressions)

usedCaseArgument ::
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues ->
  Case ->
  Map SubexpressionId SubexpressionTrace ->
  Either (ErrorMessage ann) Argument
usedCaseArgument ann tt t m fvs airFvs c es = do
  arg0 <- emptyCaseArgument ann tt t m fvs airFvs c CaseIsUsed
  args <- mapM
          (\(ri, (sId, sT)) -> subexpressionArgument ann tt t m fvs airFvs c CaseIsUsed sId sT ri)
          (zip (caseRowIndices tt c) (Map.toList es))
  pure $ mconcat args <> arg0

unusedCaseArgument ::
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues ->
  Case ->
  Either (ErrorMessage ann) Argument
unusedCaseArgument ann tt t m fvs airFvs c =
  emptyCaseArgument ann tt t m fvs airFvs c CaseIsNotUsed

emptyCaseArgument ::
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues ->
  Case ->
  CaseUsed ->
  Either (ErrorMessage ann) Argument
emptyCaseArgument ann tt t m fvs airFvs c used =
  mconcat <$> sequence
    [ voidRow ann tt t m fvs airFvs c used i
      | i <- caseRowIndices tt c
    ]

voidRow :: 
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues ->
  Case ->
  CaseUsed ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
voidRow ann tt t m fvs airFvs c used ri =
  subexpressionArgument ann tt t m fvs airFvs c used
    voidEid
    (SubexpressionTrace zero voidStepType defaultAdvice)
    ri
  where
    voidEid = 0 -- TODO: is it better not to assume void has subexpression id 0 and step type 0?
    voidStepType = 0
    defaultAdvice = getDefaultAdvice (m ^. #logicCircuit)

subexpressionArgument ::
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  FixedValues (RowIndex 'Absolute) ->
  AIRFixedValues ->
  Case ->
  CaseUsed ->
  SubexpressionId ->
  SubexpressionTrace ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
subexpressionArgument ann tt t m fvs airFvs c used sId sT ri = do
  mconcat <$> sequence
    [ traceTypeFixedValuesArgument ann tt fvs ri,
      airFixedValuesArgument ann airFvs ri,
      traceStatementValuesArgument ann tt t c ri,
      traceWitnessValuesArgument ann tt t c ri,
      subexpressionTraceValuesArgument ann tt t m c used sId sT ri
    ]

traceTypeFixedValuesArgument ::
  ann ->
  TraceType ->
  FixedValues (RowIndex 'Absolute) ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
traceTypeFixedValuesArgument ann tt fvs ri =
  mconcat <$> sequence
    [ Argument mempty . Witness
        . Map.singleton
          (CellReference ci ri)
            <$> maybe
                (Left
                  (ErrorMessage ann
                    ("traceTypeFixedValues: fixed value lookup failed: "
                      <> pack (show (ci, ri)))))
                pure
                (Map.lookup ri
                  =<< (Map.lookup ci (fvs ^. #getFixedValues)
                        <&> (^. #unFixedColumn)))
      | ci <-
          Map.keys $
            Map.filter
              (== Fixed)
              (tt ^. #columnTypes . #getColumnTypes)
    ]

airFixedValuesArgument ::
  ann ->
  AIRFixedValues ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
airFixedValuesArgument ann airFvs ri =
  maybe
    (Left (ErrorMessage ann
      ("airFixedValuesArgument: failed row lookup: " <> pack (show ri))))
    (pure . Argument mempty . Witness
      . Map.mapKeys (`CellReference` ri))
    (Map.lookup ri (airFvs ^. #unAIRFixedValues))

traceStatementValuesArgument ::
  ann ->
  TraceType ->
  Trace ->
  Case ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
traceStatementValuesArgument ann tt t c ri =
  (`Argument` Witness mempty) . Statement
    . Map.fromList <$> sequence
      [ (CellReference ci ri,)
          <$> maybe
                (Left (ErrorMessage ann "traceStatementValuesArgument"))
                pure
                (Map.lookup (c, ci)
                  (t ^. #statement . #unStatement))
        | ci <- Map.keys
            (Map.filter (== Instance)
              (tt ^. #columnTypes . #getColumnTypes))
      ]

traceWitnessValuesArgument ::
  ann ->
  TraceType ->
  Trace ->
  Case ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
traceWitnessValuesArgument ann tt t c ri =
  Argument mempty . Witness . Map.fromList <$> sequence
    [ (CellReference ci ri,)
        <$> maybe
              (Left (ErrorMessage ann
                ("traceWitnessValuesArgument: value lookup failed: " <> pack (show (c, ci)))))
              pure
              (Map.lookup (c, ci)
                (t ^. #witness . #unWitness))
      | ci <- Map.keys
          (Map.filter (== Advice)
            (tt ^. #columnTypes . #getColumnTypes)),
        -- TODO: make this less brittle; we need to select only the advice columns
        -- which came from the logic circuit, and this is a way to do it
        ci < tt ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex
    ]

subexpressionTraceValuesArgument ::
  ann ->
  TraceType ->
  Trace ->
  Mappings ->
  Case ->
  CaseUsed ->
  SubexpressionId ->
  SubexpressionTrace ->
  RowIndex 'Absolute ->
  Either (ErrorMessage ann) Argument
subexpressionTraceValuesArgument ann tt t m c used sId sT ri =
  Argument mempty . Witness . mconcat <$> sequence
    [ -- case used
      pure $
        Map.singleton
          (CellReference (m ^. #advice . #caseUsed . #unMapping) ri)
          (if used == CaseIsUsed then one else zero),
      -- step type
      pure $
        Map.fromList
          [ (CellReference ci ri,
             if sT ^. #stepType == stId then one else zero)
            | (stId, ci) <-
                Map.toList (tt ^. #stepTypeIdColumnIndices . #unStepTypeIdSelectionVector)
          ],
      -- step indicator
      pure $
        Map.singleton
          (CellReference (tt ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex) ri)
          zero,
      -- output subexpression id
      pure $
        Map.singleton
          (CellReference (m ^. #advice . #output . #unMapping) ri)
          (sId ^. #unSubexpressionId),
      -- output value
      pure $
        Map.singleton
          (CellReference (tt ^. #outputColumnIndex . #unOutputColumnIndex) ri)
          (sT ^. #value),
      -- input subexpression ids and values, and advice from subexpression trace
      do
        inIds <-
          maybe
            (Left . ErrorMessage ann
              $ "subexpressionTraceValuesArgument: link not found: "
                  <> pack (show (sT ^. #stepType, OutputSubexpressionId sId)))
            pure
            (Map.lookup
              (sT ^. #stepType, OutputSubexpressionId sId)
              (tt ^. #links))
        mconcat <$> sequence
          [ do x0 <- (CellReference inCol ri,)
                       <$> maybe
                           (Left (ErrorMessage ann "subexpressionTraceValuesArgument: input subexpression id"))
                           (pure . (^. #value))
                           (Map.lookup c (t ^. #subexpressions)
                             >>= Map.lookup inId)
               let x1 = (CellReference sIdCol ri, inId ^. #unSubexpressionId)
                   xs = (\(ci, y) -> (CellReference ci ri, y)) <$> Map.toList (sT ^. #adviceValues)
               pure (Map.fromList (x0 : x1 : xs))
            | (InputSubexpressionId inId, InputColumnIndex inCol, Mapping sIdCol) <-
                zip3 inIds (tt ^. #inputColumnIndices) (m ^. #advice . #inputs)
          ]
    ]

padInfinitely :: [a] -> [a]
padInfinitely [] = []
padInfinitely [a] = repeat a
padInfinitely (x:xs) = x : padInfinitely xs
