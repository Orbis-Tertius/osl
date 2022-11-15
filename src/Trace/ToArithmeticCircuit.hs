{-# LANGUAGE OverloadedLabels #-}

module Trace.ToArithmeticCircuit (traceTypeToArithmeticCircuit) where

import Data.List.Extra (mconcatMap)
import qualified Data.Map as Map
import Halo2.AIR (toCircuit)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import Halo2.Types.Circuit (ArithmeticCircuit)
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.Polynomial (Polynomial)
import Trace.ToArithmeticAIR (traceTypeToArithmeticAIR)
import Trace.Types (TraceType, StepTypeId, StepType)

traceTypeToArithmeticCircuit
  :: TraceType
  -> ArithmeticCircuit
traceTypeToArithmeticCircuit traceType =
  toCircuit
  (traceTypeToArithmeticAIR traceType)
  mempty
  (traceTypeLookupArguments traceType)
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
traceTypeLookupArguments
  :: TraceType
  -> LookupArguments
traceTypeLookupArguments t =
  mconcat
  [ inputChecks t,
    linkChecks t,
    resultChecks t,
    traceStepTypeLookupArguments t
  ]

inputChecks
  :: TraceType
  -> LookupArguments
inputChecks = todo

linkChecks
  :: TraceType
  -> LookupArguments
linkChecks = todo

resultChecks
  :: TraceType
  -> LookupArguments
resultChecks = todo

traceStepTypeLookupArguments
  :: TraceType
  -> LookupArguments
traceStepTypeLookupArguments t =
  mconcatMap (gatedStepTypeLookupArguments t) (Map.toList (t ^. #stepTypes))

gatedStepTypeLookupArguments
  :: TraceType
  -> (StepTypeId, StepType)
  -> LookupArguments
gatedStepTypeLookupArguments t (sId, s) =
  mconcatMap (LookupArguments . (:[]) . gateStepTypeLookupArgument t sId)
    (s ^. #lookupArguments . #getLookupArguments)

gateStepTypeLookupArgument
  :: TraceType
  -> StepTypeId
  -> LookupArgument
  -> LookupArgument
gateStepTypeLookupArgument t sId arg =
  LookupArgument
  (P.times (stepIndicatorGate t) (P.times (stepTypeGate t sId) (arg ^. #gate)))
  (arg ^. #tableMap)

stepIndicatorGate
  :: TraceType
  -> Polynomial
stepIndicatorGate t =
  P.minus (P.constant 1)
    (P.var' (t ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex))

stepTypeGate
  :: TraceType
  -> StepTypeId
  -> Polynomial
stepTypeGate = todo

todo :: a
todo = todo
