{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLabels #-}

module Trace.ToArithmeticAIR
  ( traceTypeToArithmeticAIR
  , Mapping (Mapping)
  , CaseNumber
  , One
  , Mappings (Mappings)
  , FixedMappings (FixedMappings)
  , mappings
  ) where

import Cast (scalarToInt)
import Control.Lens ((<&>))
import Data.List.Extra (mconcatMap, (!?))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Halo2.Prelude
import qualified Halo2.Polynomial as P
import Halo2.Types.AIR (AIR (AIR), ArithmeticAIR)
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Fixed, Advice))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.FixedColumn (FixedColumn (FixedColumn))
import Halo2.Types.FixedValues (FixedValues (FixedValues))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (PolynomialConstraints))
import Trace.Types (TraceType, StepTypeId, InputSubexpressionId (InputSubexpressionId), OutputSubexpressionId, StepType, StepTypeColumnIndex, SubexpressionLink, SubexpressionId (SubexpressionId))

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
  (columnTypes t)
  (gateConstraints t)
  (t ^. #rowCount)
  (additionalFixedValues t (m ^. #fixed))
  where
    m = mappings t

columnTypes :: TraceType -> ColumnTypes
columnTypes t =
  (t ^. #columnTypes)
  <> ColumnTypes
     (Map.fromList
       (zip [i..]
         (replicate (4 + n) Fixed)))
  <> ColumnTypes
     (Map.fromList
       (zip [j..] (replicate (n+1) Advice)))
  where
    i :: ColumnIndex
    i = ColumnIndex . length . Map.keys 
          $ t ^. #columnTypes . #getColumnTypes

    j :: ColumnIndex
    j = ColumnIndex $ (i ^. #getColumnIndex) + 4 + n

    n :: Int
    n = length (t ^. #inputColumnIndices)

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

data Mappings =
  Mappings
  { fixed :: FixedMappings
  , advice :: AdviceMappings
  }
  deriving Generic

data FixedMappings =
  FixedMappings
  { stepType :: Mapping StepTypeId
  , inputs :: [Mapping InputSubexpressionId]
  , output :: Mapping OutputSubexpressionId
  , caseNumber :: Mapping CaseNumber
  , one :: Mapping One
  }
  deriving Generic

data AdviceMappings =
  AdviceMappings
  { inputs :: [Mapping InputSubexpressionId]
  , output :: Mapping OutputSubexpressionId
  }
  deriving Generic

mappings :: TraceType -> Mappings
mappings t =
  Mappings
    (FixedMappings
      (Mapping i :: Mapping StepTypeId)
      (Mapping <$> [i+1..j] :: [Mapping InputSubexpressionId])
      (Mapping (j+1) :: Mapping OutputSubexpressionId)
      (Mapping (j+2) :: Mapping CaseNumber)
      (Mapping (j+3) :: Mapping One))
    (AdviceMappings
      (Mapping <$> [j+4..k] :: [Mapping InputSubexpressionId])
      (Mapping (k+1) :: Mapping OutputSubexpressionId))
  where
    i :: ColumnIndex
    i = ColumnIndex (length (Map.keys (t ^. #columnTypes . #getColumnTypes)))

    j :: ColumnIndex
    j = i + ColumnIndex n

    k :: ColumnIndex
    k = j + 4 + ColumnIndex n

    n :: Int
    n = length (t ^. #inputColumnIndices)

additionalFixedValues
  :: TraceType
  -> FixedMappings
  -> FixedValues
additionalFixedValues t m =
  linksTableFixedColumns (linksTable t) m <> caseFixedColumn t m <> oneFixedColumn t m

newtype LinksTable =
  LinksTable
    { unLinksTable :: [SubexpressionLink] }
  deriving Generic

linksTable
  :: TraceType
  -> LinksTable
linksTable = LinksTable . Set.toList . (^. #links)

linksTableFixedColumns
  :: LinksTable
  -> FixedMappings
  -> FixedValues
linksTableFixedColumns (LinksTable ls) m =
  FixedValues . Map.fromList $
  [ (m ^. #stepType . #unMapping,
      FixedColumn $ ls <&> (^. #stepType . #unStepTypeId))
  , (m ^. #output . #unMapping,
      FixedColumn $ ls <&> (^. #output . #unOutputSubexpressionId . #unSubexpressionId))
  ]
  <>
  zip ((m ^. #inputs) <&> (^. #unMapping))
      [ FixedColumn $
          fromMaybe (replicate (length ls) (InputSubexpressionId (SubexpressionId 0)))
          ((ls <&> (^. #inputs)) !? i)
          <&> (^. #unInputSubexpressionId . #unSubexpressionId)
      | i <- [0 .. length (m ^. #inputs) - 1]
      ]

caseFixedColumn
  :: TraceType
  -> FixedMappings
  -> FixedValues
caseFixedColumn t m =
  FixedValues $
  Map.singleton
    (m ^. #caseNumber . #unMapping)
    . FixedColumn $
      [0 .. (t ^. #numCases . #unNumberOfCases) - 1] <>
      (replicate (scalarToInt (t ^. #rowCount . #getRowCount)
                   - scalarToInt (t ^. #numCases . #unNumberOfCases)) 0)

oneFixedColumn
  :: TraceType
  -> FixedMappings
  -> FixedValues
oneFixedColumn t m =
  FixedValues $
  Map.singleton
    (m ^. #one . #unMapping)
    (FixedColumn (replicate (scalarToInt (t ^. #rowCount . #getRowCount)) 1))
