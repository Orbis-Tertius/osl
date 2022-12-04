{-# LANGUAGE OverloadedLabels #-}

module Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit) where

import qualified Algebra.Additive as Group
import Control.Lens ((<&>))
import Data.List.Extra (foldl', mconcatMap)
import qualified Data.Map as Map
import qualified Data.Set as Set
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
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.RowIndex (RowIndex (..))
import Stark.Types.Scalar (one, scalarToInt, zero)
import Trace.ToArithmeticAIR (Mappings, mappings, traceTypeToArithmeticAIR)
import Trace.Types (StepType, StepTypeId, TraceType)

traceTypeToArithmeticCircuit ::
  TraceType ->
  ArithmeticCircuit
traceTypeToArithmeticCircuit traceType =
  toCircuit
    (traceTypeToArithmeticAIR traceType)
    (EqualityConstrainableColumns (Set.singleton (m ^. #advice . #caseUsed . #unMapping)))
    (traceTypeLookupArguments traceType m)
    (traceTypeEqualityConstraints traceType m)
  where
    m = mappings traceType

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

inputChecks ::
  TraceType ->
  Mappings ->
  LookupArguments Polynomial
inputChecks t m =
  LookupArguments
    [ LookupArgument
        (stepIndicatorGate t)
        [ (InputExpression alpha, LookupTableColumn beta),
          (InputExpression sigma', LookupTableColumn sigma),
          (InputExpression x, LookupTableColumn y)
        ]
      | (iIdCol, iCol) <-
          zip
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
  LookupArguments
    [ LookupArgument
        (stepIndicatorGate t)
        ( zip
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
    tau = P.var' $ t ^. #stepTypeColumnIndex . #unStepTypeColumnIndex
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
  LookupArguments
    [ LookupArgument
        ( P.var' (t ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex)
            `P.minus` P.one
        )
        [ (InputExpression (P.var' traceCase), LookupTableColumn fixedCase),
          (InputExpression P.one, LookupTableColumn used)
        ],
      LookupArgument
        (P.var' used `P.minus` P.one)
        [ (InputExpression (P.var' fixedCase), LookupTableColumn traceCase),
          (InputExpression (P.var' fixedResultId), LookupTableColumn outputExpressionId)
        ]
    ]
  where
    fixedCase = m ^. #fixed . #caseNumber . #unMapping
    fixedResultId = m ^. #fixed . #result . #unMapping
    traceCase = t ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex
    outputExpressionId = m ^. #advice . #output . #unMapping
    used = m ^. #advice . #caseUsed . #unMapping

traceStepTypeLookupArguments ::
  TraceType ->
  LookupArguments Polynomial
traceStepTypeLookupArguments t =
  mconcatMap (gatedStepTypeLookupArguments t) (Map.toList (t ^. #stepTypes))

gatedStepTypeLookupArguments ::
  TraceType ->
  (StepTypeId, StepType) ->
  LookupArguments Polynomial
gatedStepTypeLookupArguments t (sId, s) =
  mconcatMap
    (LookupArguments . (: []) . gateStepTypeLookupArgument t sId)
    (s ^. #lookupArguments . #getLookupArguments)

gateStepTypeLookupArgument ::
  TraceType ->
  StepTypeId ->
  LookupArgument Polynomial ->
  LookupArgument Polynomial
gateStepTypeLookupArgument t sId arg =
  LookupArgument
    (P.plus (P.times alpha (stepIndicatorGate t)) (stepTypeGate t sId))
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
  P.var' (t ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex)

stepTypeGate ::
  TraceType ->
  StepTypeId ->
  Polynomial
stepTypeGate t sId =
  P.constant (sId ^. #unStepTypeId)
    `P.minus` P.var' (t ^. #stepTypeColumnIndex . #unStepTypeColumnIndex)

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
