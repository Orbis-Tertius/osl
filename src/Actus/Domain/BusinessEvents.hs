{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Actus.Domain.BusinessEvents where

import Data.Aeson.Types (FromJSON, ToJSON)
import GHC.Generics (Generic)

-- | ACTUS event types
--    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-event.json
data EventType
  = -- | Initial Exchange
    IED
  | -- | Fee Payment
    FP
  | -- | Principal Redemption
    PR
  | -- | Principal Drawing
    PD
  | -- | Penalty Payment
    PY
  | -- | Principal Prepayment (unscheduled event)
    PP
  | -- | Interest Payment
    IP
  | -- | Interest Payment Fixed Leg
    IPFX
  | -- | Interest Payment Floating Leg
    IPFL
  | -- | Interest Capitalization
    IPCI
  | -- | Credit Event
    CE
  | -- | Rate Reset Fixing with Known Rate
    RRF
  | -- | Rate Reset Fixing with Unknown Rate
    RR
  | -- | Principal Payment Amount Fixing
    PRF
  | -- | Dividend Payment
    DV
  | -- | Purchase
    PRD
  | -- | Margin Call
    MR
  | -- | Termination
    TD
  | -- | Scaling Index Fixing
    SC
  | -- | Interest Calculation Base Fixing
    IPCB
  | -- | Maturity
    MD
  | -- | Exercise
    XD
  | -- | Settlement
    STD
  | -- | Principal Increase
    PI
  | -- | Monitoring
    AD
  deriving stock (Eq, Show, Read, Ord, Enum, Generic)
  deriving anyclass (FromJSON, ToJSON)
