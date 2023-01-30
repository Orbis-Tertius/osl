{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-orphans #-}

module Actus.Domain.ContractState
  where

import Actus.Domain.Basic (Rational, Value, Rate)
import Actus.Domain.ContractTerms (PRF')
import Control.Lens
import Data.Time (LocalTime (..))
import OSL.FromHaskell (ToOSLType)
import Prelude hiding (Rational)

newtype DayCount = DayCount Rational
  deriving newtype (Show, Eq, ToOSLType)

newtype MD' = MD' LocalTime
  deriving newtype (Show, Eq, ToOSLType)

newtype NT = NT Value
  deriving newtype (Show, Eq, ToOSLType)

newtype IPNR = IPNR Rate
  deriving newtype (Show, Eq, ToOSLType)

newtype IPAC = IPAC Value
  deriving newtype (Show, Eq, ToOSLType)

newtype IPAC1 = IPAC1 Value
  deriving newtype (Show, Eq, ToOSLType)

newtype IPAC2 = IPAC2 Value
  deriving newtype (Show, Eq, ToOSLType)

newtype IPLA = IPLA DayCount
  deriving newtype (Show, Eq, ToOSLType)

newtype FEAC = FEAC Value
  deriving newtype (Show, Eq, ToOSLType)

newtype NSC = NSC Rational
  deriving newtype (Show, Eq, ToOSLType)

newtype ISC = ISC Rational
  deriving newtype (Show, Eq, ToOSLType)

newtype SD = SD LocalTime
  deriving newtype (Show, Eq, ToOSLType)

newtype PRNXT = PRNXT Value
  deriving newtype (Show, Eq, ToOSLType)

newtype IPCB = IPCB Rational
  deriving newtype (Show, Eq, ToOSLType)

newtype XD = XD LocalTime
  deriving newtype (Show, Eq, ToOSLType)

newtype XA = XA Value
  deriving newtype (Show, Eq, ToOSLType)

{-| ACTUS contract states are defined in
    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-states.json
-}
data ContractState = ContractState
  {
    tmd   :: Maybe MD'       -- ^ Maturity Date (MD): The timestamp as per which the contract matures according to the initial terms or as per unscheduled events
  , nt    :: NT              -- ^ Notional Principal (NT): The outstanding nominal value
  , ipnr  :: IPNR            -- ^ Nominal Interest Rate (IPNR) : The applicable nominal rate
  , ipac  :: IPAC            -- ^ Accrued Interest (IPAC): The current value of accrued interest
  , ipac1 :: Maybe IPAC1     -- ^ Accrued Interest (IPAC1): The current value of accrued interest of the first leg
  , ipac2 :: Maybe IPAC2     -- ^ Accrued Interest (IPAC2): The current value of accrued interest of the second leg
  , ipla  :: Maybe IPLA      -- ^ Last Interst Period
  , feac  :: FEAC            -- ^ Fee Accrued (FEAC): The current value of accrued fees
  , nsc   :: NSC             -- ^ Notional Scaling Multiplier (SCNT): The multiplier being applied to principal cash flows
  , isc   :: ISC             -- ^ InterestScalingMultiplier (SCIP): The multiplier being applied to interest cash flows
  , prf   :: PRF'            -- ^ Contract Performance (PRF)
  , sd    :: SD              -- ^ Status Date (MD): The timestamp as per which the state is captured at any point in time
  , prnxt :: PRNXT           -- ^ Next Principal Redemption Payment (PRNXT): The value at which principal is being repaid
  , ipcb  :: IPCB            -- ^ Interest Calculation Base (IPCB)
  , xd    :: Maybe LocalTime -- ^ Exercise Date (XD)
  , xa    :: Maybe XA        -- ^ Exercise Amount (XA)
  }
  deriving stock (Show, Eq)

makeLensesFor
  [ ("sd", "statusDate")
  , ("nt", "notionalPrincipal")
  , ("ipnr", "nominalInterest")
  , ("ipac", "accruedInterest")
  , ("ipac1", "accruedInterestFirstLeg")
  , ("ipac2", "accruedInterestSecondLeg")
  , ("ipla", "lastInterestPeriod")
  , ("ipcb", "interestCalculationBase")
  , ("feac", "accruedFees")
  , ("nsc", "notionalScalingMultiplier")
  , ("isc", "interestScalingMultiplier")
  , ("prnxt", "nextPrincipalRedemptionPayment")
  , ("xa", "exerciseAmount")
  ] ''ContractState
