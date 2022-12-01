{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit) where

import qualified Algebra.Additive as Group
import Control.Lens ((<&>))
import Data.List.Extra (foldl', mconcatMap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Die (die)
import Halo2.AIR (toCircuit)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.InputExpression (InputExpression (InputExpression))
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial)
import Stark.Types.Scalar (one, zero)
import Trace.ToArithmeticAIR (Mappings, mappings, traceTypeToArithmeticAIR)
import Trace.Types (StepType, StepTypeId, SubexpressionId, TraceType)

traceTypeToArithmeticCircuit ::
  TraceType ->
  ArithmeticCircuit
traceTypeToArithmeticCircuit traceType =
  toCircuit
    (traceTypeToArithmeticAIR traceType)
    mempty
    (traceTypeLookupArguments traceType (mappings traceType))
    mempty

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
  LookupArguments
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
  LookupArguments
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
  LookupArguments
linkChecks t m =
  LookupArguments $
    [ LookupArgument
        (stepIndicatorGate t)
        ( zip
            (InputExpression <$> ([currentCase, tau] <> alphas <> [beta]))
            (LookupTableColumn <$> links)
        )
    ]
      <> [ LookupArgument
             (P.plus (P.times gamma (stepIndicatorGate t)) (subexpressionIdGate m eidOut))
             ( zip
                 (InputExpression <$> [currentCase, P.constant $ eidIn ^. #unPreconditionSubexpressionId . #unSubexpressionId])
                 (LookupTableColumn <$> [caseNumber, subexpressionId])
             )
           | link <- Set.toList (t ^. #links),
             let eidOut = link ^. #output . #unOutputSubexpressionId,
             eidIn <- link ^. #preconditions
         ]
  where
    tau, beta, gamma, currentCase :: Polynomial
    alphas :: [Polynomial]
    links :: [ColumnIndex]
    caseNumber, subexpressionId :: ColumnIndex
    caseNumber = t ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex
    subexpressionId = m ^. #advice . #output . #unMapping
    currentCase = P.var' caseNumber
    gamma = P.constant $
      case Set.lookupMax (t ^. #subexpressions) of
        Just eid -> (eid ^. #unSubexpressionId) + one
        Nothing -> die "linkChecks: no subexpression ids (this is a compiler bug)"
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
  LookupArguments
resultChecks t m =
  LookupArguments
    [ LookupArgument
        P.zero
        [ (InputExpression i, LookupTableColumn sigma),
          (InputExpression r, LookupTableColumn tau),
          (InputExpression P.one, LookupTableColumn y)
        ]
    ]
  where
    i, r :: Polynomial
    sigma, tau, y :: ColumnIndex
    i = P.var' $ m ^. #fixed . #caseNumber . #unMapping
    r = P.constant (t ^. #result . #unResultExpressionId . #unSubexpressionId)
    sigma = t ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex
    tau = t ^. #stepTypeColumnIndex . #unStepTypeColumnIndex
    y = t ^. #outputColumnIndex . #unOutputColumnIndex

traceStepTypeLookupArguments ::
  TraceType ->
  LookupArguments
traceStepTypeLookupArguments t =
  mconcatMap (gatedStepTypeLookupArguments t) (Map.toList (t ^. #stepTypes))

gatedStepTypeLookupArguments ::
  TraceType ->
  (StepTypeId, StepType) ->
  LookupArguments
gatedStepTypeLookupArguments t (sId, s) =
  mconcatMap
    (LookupArguments . (: []) . gateStepTypeLookupArgument t sId)
    (s ^. #lookupArguments . #getLookupArguments)

gateStepTypeLookupArgument ::
  TraceType ->
  StepTypeId ->
  LookupArgument ->
  LookupArgument
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

subexpressionIdGate ::
  Mappings ->
  SubexpressionId ->
  Polynomial
subexpressionIdGate m eid =
  P.var' (m ^. #advice . #output . #unMapping)
    `P.minus` P.constant (eid ^. #unSubexpressionId)
