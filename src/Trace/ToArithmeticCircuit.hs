{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit) where

import qualified Algebra.Additive as Group
import Control.Lens ((<&>))
import Data.List.Extra (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (pack)
import Die (die)
import Halo2.AIR (toCircuit)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import Halo2.Types.CellReference (CellReference (..))
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns (..))
import Halo2.Types.EqualityConstraint (EqualityConstraint (..))
import Halo2.Types.EqualityConstraints (EqualityConstraints (..))
import Halo2.Types.InputExpression (InputExpression (InputExpression))
import Halo2.Types.Label (Label (Label))
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.RowIndex (RowIndex (..))
import Stark.Types.Scalar (one, scalarToInt, zero)
import Trace.FromLogicCircuit (Mapping)
import Trace.ToArithmeticAIR (Mappings, mappings, traceTypeToArithmeticAIR)
import Trace.Types (StepTypeId, TraceType)

traceTypeToArithmeticCircuit ::
  TraceType ->
  Mapping ->
  ArithmeticCircuit
traceTypeToArithmeticCircuit traceType lcM =
  toCircuit
    (traceTypeToArithmeticAIR traceType lcM)
    (EqualityConstrainableColumns (Set.singleton (m ^. #advice . #caseUsed . #unMapping)))
    (traceTypeLookupArguments traceType m)
    (traceTypeEqualityConstraints traceType m)
  where
    m = mappings traceType lcM

-- Trace type lookup arguments entail that:
--  * For each step of each case, for each input to the step,
--    there is a step of the same case which outputs that input.
--  * For each step of each case, its vector of input and
--    output subexpression ids is in the links table.
--  * For each case, there is a step of the result
--    subexpression id and its output is 1.
-- They also include the lookup arguments for each step type,
-- gated by the step type.
traceTypeLookupArguments ::
  TraceType ->
  Mappings ->
  LookupArguments Polynomial
traceTypeLookupArguments t m =
  mconcat
    [ inputChecks t m,
      linkChecks t m,
      resultChecks t m,
      traceStepTypeLookupArguments t
    ]

-- Checks that each step's input advice columns contain
-- the outputs of the steps which should be its inputs
-- according to the links table.
inputChecks ::
  TraceType ->
  Mappings ->
  LookupArguments Polynomial
inputChecks t m =
  LookupArguments $
    Set.fromList
      [ LookupArgument
          (Label ("input-" <> show i))
          -- Only apply the check to rows which represent
          -- a step in the trace.
          (stepIndicatorGate t)
          -- alpha is the input subexpression id of the current row
          -- beta is the output subexpression id column
          [ (InputExpression alpha, LookupTableColumn beta),
            -- sigma' is the current case number
            -- sigma is the case number column
            (InputExpression sigma', LookupTableColumn sigma),
            -- x is the output value of the current row
            -- y is the output value column
            (InputExpression x, LookupTableColumn y)
          ]
        | (i, iIdCol, iCol) <-
            zip3
              ([0 ..] :: [Integer])
              ((m ^. #advice . #inputs) <&> (^. #unMapping))
              ((t ^. #inputColumnIndices) <&> (^. #unInputColumnIndex)),
          let alpha = P.var' iIdCol,
          let beta = m ^. #advice . #output . #unMapping,
          let sigma = t ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex,
          let sigma' = P.var' sigma,
          let x = P.var' iCol,
          let y = t ^. #outputColumnIndex . #unOutputColumnIndex
      ]

linkChecks ::
  TraceType ->
  Mappings ->
  LookupArguments Polynomial
linkChecks t m =
  LookupArguments $
    Set.fromList
      [ LookupArgument
          "linkCheck"
          -- applies only at rows that represent steps in the trace
          (stepIndicatorGate t)
          ( zip
              -- tau is the step type id
              -- alphas are the input subexpression ids
              -- beta is the output subexpression id
              (InputExpression <$> ([currentCase, tau] <> alphas <> [beta]))
              (LookupTableColumn <$> links)
          )
      ]
  where
    tau, beta, currentCase :: Polynomial
    alphas :: [Polynomial]
    links :: [ColumnIndex]
    caseNumber, subexpressionId :: ColumnIndex
    caseNumber = t ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex
    subexpressionId = m ^. #advice . #output . #unMapping
    currentCase = P.var' caseNumber
    -- TODO: check that the selection vector values are all in {0,1}
    tau =
      foldr
        P.plus
        P.zero
        [ P.constant (stId ^. #unStepTypeId) `P.times` P.var' ci
          | (stId, ci) <- Map.toList (t ^. #stepTypeIdColumnIndices . #unStepTypeIdSelectionVector)
        ]
    alphas = P.var' <$> ((m ^. #advice . #inputs) <&> (^. #unMapping))
    beta = P.var' subexpressionId
    links =
      [caseNumber, m ^. #fixed . #stepType . #unMapping]
        <> ((m ^. #fixed . #inputs) <&> (^. #unMapping))
        <> [m ^. #fixed . #output . #unMapping]

resultChecks ::
  TraceType ->
  Mappings ->
  LookupArguments Polynomial
resultChecks t m =
  LookupArguments $
    Set.fromList
      [ LookupArgument
          "resultCheck1"
          ( P.var' (t ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex)
              `P.minus` P.one
          )
          [ (InputExpression (P.var' traceCase), LookupTableColumn fixedCase),
            (InputExpression P.one, LookupTableColumn used)
          ],
        LookupArgument
          "resultCheck2"
          (P.one `P.minus` P.var' used)
          [ (InputExpression (P.var' fixedCase), LookupTableColumn traceCase),
            (InputExpression (P.var' fixedResultId), LookupTableColumn outputExpressionId)
          ]
      ]
  where
    fixedCase = traceCase
    fixedResultId = m ^. #fixed . #result . #unMapping
    traceCase = t ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex
    outputExpressionId = m ^. #advice . #output . #unMapping
    used = m ^. #advice . #caseUsed . #unMapping

traceStepTypeLookupArguments ::
  TraceType ->
  LookupArguments Polynomial
traceStepTypeLookupArguments t =
  gatedStepTypeLookupArguments t argMap
  where
    args :: LookupArguments Polynomial
    args = mconcat (Map.elems (t ^. #stepTypes) <&> (^. #lookupArguments))

    argMap :: Map (LookupArgument Polynomial) (Set StepTypeId)
    argMap =
      Map.fromList
        [ (arg, Map.keysSet (Map.filter ((arg `Set.member`) . (^. #lookupArguments . #getLookupArguments)) (t ^. #stepTypes)))
          | arg <- Set.toList (args ^. #getLookupArguments)
        ]

gatedStepTypeLookupArguments ::
  TraceType ->
  Map (LookupArgument Polynomial) (Set StepTypeId) ->
  LookupArguments Polynomial
gatedStepTypeLookupArguments t argMap =
  LookupArguments $
    Set.fromList
      [ gateStepTypeLookupArgument t sIds arg
        | (arg, sIds) <- Map.toList argMap
      ]

gateStepTypeLookupArgument ::
  TraceType ->
  Set StepTypeId ->
  LookupArgument Polynomial ->
  LookupArgument Polynomial
gateStepTypeLookupArgument t sIds arg =
  LookupArgument
    (arg ^. #label)
    (P.plus (P.times alpha (stepIndicatorGate t)) (stepTypesGate t sIds))
    (arg ^. #tableMap)
  where
    alpha =
      P.constant $
        foldl'
          max
          zero
          (Map.keys (t ^. #stepTypes) <&> (^. #unStepTypeId))
          Group.+ one

stepIndicatorGate ::
  TraceType ->
  Polynomial
stepIndicatorGate t =
  P.one `P.minus` P.var' (t ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex)

stepTypeGate ::
  TraceType ->
  StepTypeId ->
  Polynomial
stepTypeGate t sId =
  maybe
    ( die
        ( "Trace.ToArithmeticCircuit.stepTypeGate: column index lookup failed: "
            <> pack (show (sId, t))
        )
    )
    P.var'
    (Map.lookup sId (t ^. #stepTypeIdColumnIndices . #unStepTypeIdSelectionVector))

stepTypesGate ::
  TraceType ->
  Set StepTypeId ->
  Polynomial
stepTypesGate t sIds =
  P.one
    `P.minus` foldl' P.plus P.zero [stepTypeGate t sId | sId <- Set.toList sIds]

traceTypeEqualityConstraints ::
  TraceType ->
  Mappings ->
  EqualityConstraints
traceTypeEqualityConstraints t m =
  EqualityConstraints
    [ EqualityConstraint . Set.fromList $
        [ CellReference
            (m ^. #advice . #caseUsed . #unMapping)
            (RowIndex (caseNum * nResults + resultNum))
          | resultNum <- [0 .. nResults - 1]
        ]
      | caseNum <- [0 .. nCases - 1]
    ]
  where
    nCases = scalarToInt (t ^. #numCases . #unNumberOfCases)
    nResults = Set.size (t ^. #results)
