{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module OSL.ActusDictionary (actusDictionary, actusNameList, actusDictionaryFormatted) where

import Actus.Domain.Basic (Denominator, FEAC, Numerator, Rate, Rational, Value)
import Actus.Domain.BusinessEvents (EventType (..))
import Actus.Domain.ContractState (ContractState, DayCount, IPAC, IPAC1, IPAC2, IPCB, IPLA, IPNR, ISC, MD', NSC, NT, PRNXT, SD, XA, XD)
import Actus.Domain.ContractTerms (Assertion (..), AssertionContext, Assertions (..), BDC (..), CEGE (..), CETC (..), COCE (..), CR (..), CT (..), Calendar (..), CalendarType (..), ContractIdentifier (..), ContractStructure (..), ContractTerms (..), Cycle (..), DCC (..), DS (..), EOMC (..), ExerciseAmount (..), ExpectedNPV (..), FEB (..), FeeRate (..), FuturesPrice (..), IPCB' (..), IPCBA (..), ISM (..), Identifier (..), InterestAccrued (..), LifeCap (..), LifeFloor (..), MarketObjectCode (..), MarketObjectCodeOfRateReset (..), NextDividendPaymentAmount (..), NextPrincipalRedemptionPayment (..), NextResetRate (..), NominalRate (..), NominalRate2 (..), NotionalPrincipal (..), NotionalScalingMultiplier (..), OPTP (..), OPXT (..), OptionStrike1 (..), PPEF (..), PRF' (..), PYTP (..), PenaltyRate (..), Period (..), PeriodCap (..), PeriodFloor (..), PremiumDiscountAtIED (..), PriceAtPurchaseDate (..), PriceAtTerminationDate (..), Quantity (..), RRMOMax (..), RRMOMin (..), RateMultiplier (..), RateSpread (..), Reference (..), ReferenceRole (..), ReferenceType (..), SCEF (..), ScalingIndexAtStatusDate (..), ScheduleConfig (..), Stub (..), ZeroRiskInterest (..))
import Control.Monad.State (State, execState)
import Data.Proxy (Proxy (Proxy))
import Data.Time (LocalTime (..), TimeOfDay (..))
import OSL.Format (formatContext)
import OSL.FromHaskell (AddToOSLContext, Newtype, addToOSLContextM, mkDataToAddOSL)
import OSL.Types.OSL (ContextType (Global), Name, ValidContext)
import Prelude hiding (Rational)

mkDataToAddOSL "Bool"
mkDataToAddOSL "EventType"
mkDataToAddOSL "ContractState"
mkDataToAddOSL "CT"
mkDataToAddOSL "CR"
mkDataToAddOSL "DCC"
mkDataToAddOSL "EOMC"
mkDataToAddOSL "BDC"
mkDataToAddOSL "Calendar"
mkDataToAddOSL "ScheduleConfig"
mkDataToAddOSL "CETC"
mkDataToAddOSL "CEGE"
mkDataToAddOSL "FEB"
mkDataToAddOSL "IPCB'"
mkDataToAddOSL "SCEF"
mkDataToAddOSL "PYTP"
mkDataToAddOSL "OPTP"
mkDataToAddOSL "OPXT"
mkDataToAddOSL "DS"
mkDataToAddOSL "PPEF"
mkDataToAddOSL "CalendarType"
mkDataToAddOSL "Period"
mkDataToAddOSL "Stub"
mkDataToAddOSL "Cycle"
mkDataToAddOSL "AssertionContext"
mkDataToAddOSL "Assertion"
mkDataToAddOSL "Assertions"
mkDataToAddOSL "ReferenceType"
mkDataToAddOSL "ReferenceRole"
mkDataToAddOSL "Identifier"
mkDataToAddOSL "ContractTerms"
mkDataToAddOSL "Reference"
mkDataToAddOSL "ContractStructure"

actusDictionaryFormatted :: String
actusDictionaryFormatted = formatContext actusDictionary actusNameList

actusDictionary :: ValidContext Global ()
actusDictionary = flip execState mempty $ do
  add (Proxy @Bool)
  add (Proxy @TimeOfDay)
  add (Proxy @LocalTime)
  add (Proxy @EventType)
  add (Proxy @PRF')
  add (Proxy @(Newtype Numerator))
  add (Proxy @(Newtype Denominator))
  add (Proxy @(Newtype Rational))
  add (Proxy @(Newtype Value))
  add (Proxy @(Newtype Rate))
  add (Proxy @(Newtype DayCount))
  add (Proxy @(Newtype MD'))
  add (Proxy @(Newtype NT))
  add (Proxy @(Newtype IPNR))
  add (Proxy @(Newtype IPAC))
  add (Proxy @(Newtype IPAC1))
  add (Proxy @(Newtype IPAC2))
  add (Proxy @(Newtype IPLA))
  add (Proxy @(Newtype FEAC))
  add (Proxy @(Newtype NSC))
  add (Proxy @(Newtype ISC))
  add (Proxy @(Newtype SD))
  add (Proxy @(Newtype PRNXT))
  add (Proxy @(Newtype IPCB))
  add (Proxy @(Newtype XD))
  add (Proxy @(Newtype XA))
  add (Proxy @ContractState)
  add (Proxy @CT)
  add (Proxy @CR)
  add (Proxy @DCC)
  add (Proxy @EOMC)
  add (Proxy @BDC)
  add (Proxy @Calendar)
  add (Proxy @ScheduleConfig)
  add (Proxy @CETC)
  add (Proxy @CEGE)
  add (Proxy @FEB)
  add (Proxy @IPCB')
  add (Proxy @SCEF)
  add (Proxy @PYTP)
  add (Proxy @OPTP)
  add (Proxy @OPXT)
  add (Proxy @DS)
  add (Proxy @PPEF)
  add (Proxy @CalendarType)
  add (Proxy @Period)
  add (Proxy @Stub)
  add (Proxy @Cycle)
  add (Proxy @(Newtype RRMOMax))
  add (Proxy @(Newtype RRMOMin))
  add (Proxy @(Newtype ZeroRiskInterest))
  add (Proxy @(Newtype ExpectedNPV))
  add (Proxy @AssertionContext)
  add (Proxy @Assertion)
  add (Proxy @ReferenceType)
  add (Proxy @ReferenceRole)
  add (Proxy @(Newtype MarketObjectCode))
  add (Proxy @(Newtype ContractIdentifier))
  add (Proxy @(Newtype COCE))
  add (Proxy @(Newtype FeeRate))
  add (Proxy @(Newtype InterestAccrued))
  add (Proxy @(Newtype IPCBA))
  add (Proxy @(Newtype NominalRate))
  add (Proxy @(Newtype NominalRate2))
  add (Proxy @(Newtype ISM))
  add (Proxy @(Newtype NotionalPrincipal))
  add (Proxy @(Newtype PremiumDiscountAtIED))
  add (Proxy @(Newtype NextPrincipalRedemptionPayment))
  add (Proxy @(Newtype PriceAtPurchaseDate))
  add (Proxy @(Newtype PriceAtTerminationDate))
  add (Proxy @(Newtype ScalingIndexAtStatusDate))
  add (Proxy @(Newtype NotionalScalingMultiplier))
  add (Proxy @(Newtype Quantity))
  add (Proxy @(Newtype OptionStrike1))
  add (Proxy @(Newtype ExerciseAmount))
  add (Proxy @(Newtype FuturesPrice))
  add (Proxy @(Newtype PenaltyRate))
  add (Proxy @(Newtype NextResetRate))
  add (Proxy @(Newtype RateSpread))
  add (Proxy @(Newtype RateMultiplier))
  add (Proxy @(Newtype PeriodFloor))
  add (Proxy @(Newtype PeriodCap))
  add (Proxy @(Newtype LifeCap))
  add (Proxy @(Newtype LifeFloor))
  add (Proxy @(Newtype MarketObjectCodeOfRateReset))
  add (Proxy @(Newtype NextDividendPaymentAmount))
  add (Proxy @Identifier)
  add (Proxy @ContractTerms)
  add (Proxy @Reference)
  add (Proxy @ContractStructure)
  where
    add :: forall a. AddToOSLContext a => Proxy a -> State (ValidContext Global ()) ()
    add = addToOSLContextM

actusNameList :: [Name]
actusNameList =
  [ "TimeOfDay",
    "LocalTime",
    -- contract performance
    "PRF_PF",
    "PRF_DL",
    "PRF_DQ",
    "PRF_DF",
    "PRF'",
    -- event types
    "IED",
    "FP",
    "PR",
    "PD",
    "PY",
    "PP",
    "IP",
    "IPFX",
    "IPFL",
    "IPCI",
    "CE",
    "RRF",
    "RR",
    "PRF",
    "DV",
    "PRD",
    "MR",
    "TD",
    "SC",
    "IPCB",
    "MD",
    "XD",
    "STD",
    "PI",
    "AD",
    "EventType",
    "Numerator",
    "Denominator",
    "Rational",
    "Value",
    "Rate",
    "Period",
    "MD'",
    "NT",
    "IPNR",
    "IPAC",
    "IPAC1",
    "IPAC2",
    "IPLA",
    "FEAC",
    "NSC",
    "ISC",
    "SD",
    "PRNXT",
    "IPCB",
    "XD",
    "XA",
    "ContractState",
    -- contract types
    "PAM",
    "LAM",
    "NAM",
    "ANN",
    "STK",
    "OPTNS",
    "FUTUR",
    "COM",
    "CSH",
    "CLM",
    "SWPPV",
    "SWAPS",
    "CEG",
    "CEC",
    "CT",
    -- contract roles
    "CR_RPA",
    "CR_RPL",
    "CR_CLO",
    "CR_CNO",
    "CR_COL",
    "CR_LG",
    "CR_ST",
    "CR_BUY",
    "CR_SEL",
    "CR_RFL",
    "CR_PFL",
    "CR_RF",
    "CR_PF",
    "CR",
    -- day count conventions
    "DCC_A_AISDA",
    "DCC_A_360",
    "DCC_A_365",
    "DCC_E30_360ISDA",
    "DCC_E30_360",
    "DCC_B_252",
    "DCC",
    -- end of month conventions
    "EOMC_EOM",
    "EOMC_SD",
    "EOMC",
    -- business day conventions
    "BDC_NULL",
    "BDC_SCF",
    "BDC_SCMF",
    "BDC_CSF",
    "BDC_CSMF",
    "BDC_SCP",
    "BDC_SCMP",
    "BDC_CSP",
    "BDC_CSMP",
    "BDC",
    -- calendar
    "CLDR_MF",
    "CLDR_NC",
    "Calendar",
    "ScheduleConfig",
    -- credit event type covered
    "CETC_DL",
    "CETC_DQ",
    "CETC_DF",
    "CETC",
    -- guaranteed exposure
    "CEGE_NO",
    "CEGE_NI",
    "CEGE",
    -- fee basis
    "FEB_A",
    "FEB_N",
    "FEB",
    -- interest calculation base
    "IPCB_NT",
    "IPCB_NTIED",
    "IPCB_NTL",
    "IPCB'",
    -- scaling effects
    "SE_OOO",
    "SE_IOO",
    "SE_IOO",
    "SE_ONO",
    "SE_OOM",
    "SE_INO",
    "SE_ONM",
    "SE_IOM",
    "SE_INM",
    "SCEF",
    -- penalty types
    "PYTP_A",
    "PYTP_N",
    "PYTP_I",
    "PYTP_O",
    "PYTP",
    -- option types
    "OPTP_C",
    "OPTP_P",
    "OPTP_CP",
    "OPTP",
    -- option exercise types
    "OPXT_E",
    "OPXT_B",
    "OPXT_A",
    -- settlement
    "DS_S",
    "DS_D",
    "DS",
    -- prepayment effects
    "PPEF_N",
    "PPEF_A",
    "PPEF_M",
    "PPEF",
    -- calendar type
    "NoCalendar",
    "MondayToFriday",
    "CustomCalendar",
    "CalendarType",
    -- cycle period
    "P_D",
    "P_W",
    "P_M",
    "P_Q",
    "P_H",
    "P_Y",
    "Period",
    -- cycle stubs
    "ShortStub",
    "LongStub",
    "Stub",
    "Cycle",
    -- assertion contexts & assertions
    "RRMOMin",
    "RRMOMax",
    "AssertionContext",
    "NpvAssertionAgainstZeroRiskBond",
    "Assertion",
    -- reference types
    "CNT",
    "CID",
    "MOC",
    "EID",
    "CST",
    "ReferenceType",
    -- reference roles
    "UDL",
    "FIL",
    "SEL",
    "COVE",
    "COVI",
    "ReferenceRole",
    "MarketObjectCode",
    "ContractIdentifier",
    "COCE",
    "FeeRate",
    "InterestAccrued",
    "IPCBA",
    "NominalRate",
    "NominalRate2",
    "ISM",
    "NotionalPrincipal",
    "PremiumDiscountAtIED",
    "NextPrincipalRedemptionPayment",
    "PriceAtPurchaseDate",
    "PriceAtTerminationDate",
    "ScalingIndexAtStatusDate",
    "NotionalScalingMultiplier",
    "Quantity",
    "OptionStrike1",
    "ExerciseAmount",
    "FuturesPrice",
    "PenaltyRate",
    "NextResetRate",
    "RateSpread",
    "RateMultiplier",
    "PeriodFloor",
    "PeriodCap",
    "LifeCap",
    "LifeFloor",
    "MarketObjectCodeOfRateReset",
    "NextDividendPaymentAmount",
    "Identifier",
    "ContractTerms",
    "Reference",
    "ContractStructure"
  ]