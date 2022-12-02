{-# LANGUAGE OverloadedLabels #-}

module Trace.Metrics (getTraceTypeMetrics) where

import Control.Lens ((^.))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Trace.Types (TraceType)
import Trace.Types.Metrics (InputColumnCount (..), LinkCount (..), ResultCount (..), StepTypeCount (..), SubexpressionCount (..), TraceTypeMetrics (..))

getTraceTypeMetrics :: TraceType -> TraceTypeMetrics
getTraceTypeMetrics t =
  TraceTypeMetrics
    (StepTypeCount (Map.size (t ^. #stepTypes)))
    (SubexpressionCount (Set.size (t ^. #subexpressions)))
    (LinkCount (Set.size (t ^. #links)))
    (ResultCount (Set.size (t ^. #results)))
    (InputColumnCount (length (t ^. #inputColumnIndices)))
    (t ^. #numCases)
