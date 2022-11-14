{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}

module Trace.ToArithmeticAIR
  ( traceTypeToArithmeticAIR
  , Mapping (Mapping)
  , CaseNumber
  , One
  , FixedValueMappings (FixedValueMappings)
  , fixedValueMappings
  ) where

import Data.List.Extra (mconcatMap)
import qualified Data.Map as Map
import Halo2.Prelude
import qualified Halo2.Polynomial as P
import Halo2.Types.AIR (AIR (AIR), ArithmeticAIR)
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Fixed))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (PolynomialConstraints))
import Trace.Types (TraceType, StepTypeId, InputSubexpressionId, OutputSubexpressionId, StepType, StepTypeColumnIndex)

-- Trace type arithmetic AIRs have the columnar structure
-- of the trace type, with additional fixed columns for:
--  * the table of links, and
--  * the table {(i,1) | i < numCases}.
--
-- Trace type arithmetic AIR gate constraints entail that
-- for each step of each case, the gate constraints of
-- its step type are satisfied.
traceTypeToArithmeticAIR :: TraceType -> ArithmeticAIR
traceTypeToArithmeticAIR t =
  AIR
  (columnTypes t m)
  (gateConstraints t)
  (t ^. #rowCount)
  (additionalFixedValues t m)
  where
    m = fixedValueMappings t

columnTypes :: TraceType -> FixedValueMappings -> ColumnTypes
columnTypes t m =
  (t ^. #columnTypes)
  <> ColumnTypes
     (Map.fromList
       (zip
         (ColumnIndex <$>
           [length . Map.keys 
             $ t ^. #columnTypes . #getColumnTypes])
         (replicate (4 + length (m ^. #inputs)) Fixed)))

gateConstraints :: TraceType -> PolynomialConstraints
gateConstraints t =
  mconcatMap
    (stepTypeGateConstraints (t ^. #stepTypeColumnIndex))
    (Map.toList (t ^. #stepTypes))

stepTypeGateConstraints :: StepTypeColumnIndex -> (StepTypeId, StepType) -> PolynomialConstraints
stepTypeGateConstraints i (tId, t) =
  PolynomialConstraints
  (gateOnStepType i tId <$> (t ^. #gateConstraints . #constraints))
  (t ^. #gateConstraints . #degreeBound)

gateOnStepType :: StepTypeColumnIndex -> StepTypeId -> Polynomial -> Polynomial
gateOnStepType i tId =
  P.times
    (P.minus
      (P.var' (i ^. #unStepTypeColumnIndex))
      (P.constant (tId ^. #unStepTypeId)))

newtype Mapping a =
  Mapping { unMapping :: ColumnIndex }
  deriving Generic

data CaseNumber

data One

data FixedValueMappings =
  FixedValueMappings
  { stepType :: Mapping StepTypeId
  , inputs :: [Mapping InputSubexpressionId]
  , output :: Mapping OutputSubexpressionId
  , caseNumber :: Mapping CaseNumber
  , one :: Mapping One
  }
  deriving Generic

fixedValueMappings :: TraceType -> FixedValueMappings
fixedValueMappings t =
  FixedValueMappings
  (Mapping i :: Mapping StepTypeId)
  (Mapping <$> [i+1..j] :: [Mapping InputSubexpressionId])
  (Mapping (j+1) :: Mapping OutputSubexpressionId)
  (Mapping (j+2) :: Mapping CaseNumber)
  (Mapping (j+3) :: Mapping One)
  where
    i :: ColumnIndex
    i = ColumnIndex (length (Map.keys (t ^. #columnTypes . #getColumnTypes)))

    j :: ColumnIndex
    j = i + 1
      + ColumnIndex (Map.foldl' max 0
                       (length . (^. #inputs)
                         <$> (t ^. #stepTypes)))

additionalFixedValues
  :: TraceType
  -> FixedValueMappings
  -> FixedValues
additionalFixedValues = todo

todo :: a
todo = todo
