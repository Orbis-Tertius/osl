{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Trace.Types.Metrics
  ( TraceTypeMetrics (TraceTypeMetrics),
    StepTypeCount (StepTypeCount),
    NumberOfCases (NumberOfCases),
    SubexpressionCount (SubexpressionCount),
    LinkCount (LinkCount),
    ResultCount (ResultCount),
    InputColumnCount (InputColumnCount),
  )
where

import GHC.Generics (Generic)
import Trace.Types (NumberOfCases (NumberOfCases))

newtype StepTypeCount = StepTypeCount {unStepTypeCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype SubexpressionCount = SubexpressionCount {unSubexpressionCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype LinkCount = LinkCount {unLinkCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype ResultCount = ResultCount {unResultCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

newtype InputColumnCount = InputColumnCount {unInputColumnCount :: Int}
  deriving stock (Generic)
  deriving newtype (Show)

data TraceTypeMetrics = TraceTypeMetrics
  { stepTypeCount :: StepTypeCount,
    subexpressionCount :: SubexpressionCount,
    linkCount :: LinkCount,
    resultCount :: ResultCount,
    inputColumnCount :: InputColumnCount,
    numCases :: NumberOfCases
  }
  deriving stock (Generic, Show)
