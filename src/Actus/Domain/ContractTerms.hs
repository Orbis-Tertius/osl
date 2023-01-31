{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Actus.Domain.ContractTerms where

import Actus.Domain.Basic (FEAC, Rate, Rational, Value)
import Control.Applicative ((<|>))
import Control.Monad (guard, mzero)
import Data.Aeson.TH (deriveJSON)
import Data.Aeson.Types
  ( FromJSON,
    Key,
    Object,
    Options (..),
    Parser,
    SumEncoding (..),
    ToJSON,
    Value (..),
    defaultOptions,
    genericParseJSON,
    object,
    parseJSON,
    toJSON,
    (.:),
    (.:?),
    (.=),
  )
import Data.Maybe (fromMaybe)
import Data.Text as T hiding (reverse, takeWhile)
import Data.Text.Read as T
import Data.Time (Day, LocalTime)
import GHC.Generics (Generic)
import OSL.FromHaskell (ToOSLType, mkDataToAddOSL)
import Prelude hiding (Rational)

-- | ContractType
data CT
  = -- | Principal at maturity
    PAM
  | -- | Linear amortizer
    LAM
  | -- | Negative amortizer
    NAM
  | -- | Annuity
    ANN
  | -- | Stock
    STK
  | -- | Option
    OPTNS
  | -- | Future
    FUTUR
  | -- | Commodity
    COM
  | -- | Cash
    CSH
  | -- | Call Money
    CLM
  | -- | Plain Vanilla Swap
    SWPPV
  | -- | Swap
    SWAPS
  | -- | Guarantee
    CEG
  | -- | Collateral
    CEC
  deriving stock (Show, Read, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | ContractRole
data CR
  = -- | Real position asset
    CR_RPA
  | -- | Real position liability
    CR_RPL
  | -- | Role of a collateral
    CR_CLO
  | -- | Role of a close-out-netting
    CR_CNO
  | -- | Role of an underlying to a collateral
    CR_COL
  | -- | Long position
    CR_LG
  | -- | Short position
    CR_ST
  | -- | Protection buyer
    CR_BUY
  | -- | Protection seller
    CR_SEL
  | -- | Receive first leg
    CR_RFL
  | -- | Pay first leg
    CR_PFL
  | -- | Receive fix leg
    CR_RF
  | -- | Pay fix leg
    CR_PF
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''CR)

-- | DayCountConvention
data DCC
  = -- | Actual/Actual ISDA
    DCC_A_AISDA
  | -- | Actual/360
    DCC_A_360
  | -- | Actual/365
    DCC_A_365
  | -- | 30E/360 ISDA
    DCC_E30_360ISDA
  | -- | 30E/360
    DCC_E30_360
  | -- | Business / 252
    DCC_B_252
  deriving stock (Show, Read, Eq, Generic)

instance ToJSON DCC where
  toJSON DCC_A_AISDA = String "AA"
  toJSON DCC_A_360 = String "A360"
  toJSON DCC_A_365 = String "A365"
  toJSON DCC_E30_360ISDA = String "30E360ISDA"
  toJSON DCC_E30_360 = String "30E360"
  toJSON DCC_B_252 = String "B252"

instance FromJSON DCC where
  parseJSON (String "AA") = pure DCC_A_AISDA
  parseJSON (String "A360") = pure DCC_A_360
  parseJSON (String "A365") = pure DCC_A_365
  parseJSON (String "30E360ISDA") = pure DCC_E30_360ISDA
  parseJSON (String "30E360") = pure DCC_E30_360
  parseJSON (String "B252") = pure DCC_B_252
  parseJSON _ = mzero

-- | EndOfMonthConvention
data EOMC
  = -- | End of month
    EOMC_EOM
  | -- | Same day
    EOMC_SD
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''EOMC)

-- | BusinessDayConvention
data BDC
  = -- | No shift
    BDC_NULL
  | -- | Shift/calculate following
    BDC_SCF
  | -- | Shift/calculate modified following
    BDC_SCMF
  | -- | Calculate/shift following
    BDC_CSF
  | -- | Calculate/shift modified following
    BDC_CSMF
  | -- | Shift/calculate preceding
    BDC_SCP
  | -- | Shift/calculate modified preceding
    BDC_SCMP
  | -- | Calculate/shift preceding
    BDC_CSP
  | -- | Calculate/shift modified preceding
    BDC_CSMP
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''BDC)

data Calendar
  = -- | Monday to Friday
    CLDR_MF
  | -- | No calendar
    CLDR_NC
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''Calendar)

data ScheduleConfig = ScheduleConfig
  { calendar :: Maybe Calendar,
    endOfMonthConvention :: Maybe EOMC,
    businessDayConvention :: Maybe BDC
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | ContractPerformance
data PRF'
  = -- | Performant
    PRF_PF
  | -- | Delayed
    PRF_DL
  | -- | Delinquent
    PRF_DQ
  | -- | Default
    PRF_DF
  deriving stock (Show, Read, Eq, Generic)

$(mkDataToAddOSL "PRF'")

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''PRF')

-- | CreditEventTypeCovered
data CETC
  = -- | Delayed
    CETC_DL
  | -- | Delinquent
    CETC_DQ
  | -- | Default
    CETC_DF
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''CETC)

-- | GuaranteedExposure
data CEGE
  = -- | Nominal value
    CEGE_NO
  | -- | Nominal value plus interest
    CEGE_NI
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''CEGE)

-- | FeeBasis
data FEB
  = -- | Absolute value
    FEB_A
  | -- | Notional of underlying
    FEB_N
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''FEB)

-- | InterestCalculationBase
data IPCB'
  = -- | Calculation base always equals to NT
    IPCB_NT
  | -- | Notional remains constant amount as per IED
    IPCB_NTIED
  | -- | Calculation base is notional base laged
    IPCB_NTL
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''IPCB')

-- | ScalingEffect
data SCEF
  = -- | No scaling
    SE_OOO
  | -- | Only interest payments scaled
    SE_IOO
  | -- | Only nominal payments scaled
    SE_ONO
  | -- | Only maximum deferred amount scaled
    SE_OOM
  | -- | Interest and nominal payments scaled
    SE_INO
  | -- | Nominal and maximum deferred amount scaled
    SE_ONM
  | -- | Interest and maximum deferred amount scaled
    SE_IOM
  | -- | Interest, nominal and maximum deferred amount scaled
    SE_INM
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''SCEF)

-- | PenaltyType
data PYTP
  = -- | Absolute
    PYTP_A
  | -- | Nominal rate
    PYTP_N
  | -- | Current interest rate differential
    PYTP_I
  | -- | No penalty
    PYTP_O
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''PYTP)

-- | Option Type
data OPTP
  = -- | Call Option
    OPTP_C
  | -- | Put Option
    OPTP_P
  | -- | Call-Put Option
    OPTP_CP
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''OPTP)

-- | Option Exercise Type
data OPXT
  = -- | European
    OPXT_E
  | -- | Bermudan
    OPXT_B
  | -- | American
    OPXT_A
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''OPXT)

-- | Settlement
data DS
  = -- | Cash Settlement
    DS_S
  | -- | Physical Settlement
    DS_D
  deriving stock (Show, Read, Eq, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''DS)

-- | PrepaymentEffect
data PPEF
  = -- | No prepayment
    PPEF_N
  | -- | Prepayment allowed, prepayment results in reduction of PRNXT while MD remains
    PPEF_A
  | -- | Prepayment allowed, prepayment results in reduction of MD while PRNXT remains
    PPEF_M
  deriving stock (Show, Read, Eq, Ord, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''PPEF)

data CalendarType
  = NoCalendar
  | MondayToFriday
  | CustomCalendar {holidays :: [Day]}
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | CyclePeriod
data Period
  = -- | Day
    P_D
  | -- | Week
    P_W
  | -- | Month
    P_M
  | -- | Quarter
    P_Q
  | -- | Half year
    P_H
  | -- | Year
    P_Y
  deriving stock (Show, Read, Eq, Ord, Generic)

$(deriveJSON defaultOptions {constructorTagModifier = reverse . takeWhile (/= '_') . reverse} ''Period)

-- | CycleStub
data Stub
  = -- | Short last stub
    ShortStub
  | -- | Long last stub
    LongStub
  deriving stock (Show, Eq, Ord, Generic)

instance ToJSON Stub where
  toJSON ShortStub = String "1"
  toJSON LongStub = String "0"

instance FromJSON Stub where
  parseJSON (String "1") = pure ShortStub
  parseJSON (String "0") = pure LongStub
  parseJSON _ = mzero

-- | Cycle
data Cycle = Cycle
  { n :: Integer,
    p :: Period,
    stub :: Stub,
    includeEndDay :: Bool
  }
  deriving stock (Show, Eq, Ord, Generic)

instance ToJSON Cycle where
  toJSON (Cycle n p s _) =
    case toJSON p of
      String p' ->
        case toJSON s of
          String s' ->
            String $
              'P'
                `cons` pack (show n)
                `append` p'
                `snoc` 'L'
                `append` s'
          _ -> Null
      _ -> Null

instance FromJSON Cycle where
  parseJSON (String s) = fromMaybe mzero (parseCycle s)
    where
      parseCycle :: Text -> Maybe (Parser Cycle)
      parseCycle c = do
        r0 <- unconsConstant 'P' c
        (n, r1) <- hush $ T.decimal r0
        (p, r2) <- uncons r1
        if T.null r2
          then
            Just $
              Cycle n
                <$> parseJSON (String $ singleton p)
                <*> pure LongStub
                <*> pure False
          else do
            r3 <- unconsConstant 'L' r2
            Just $
              Cycle n
                <$> parseJSON (String $ singleton p)
                <*> parseJSON (String r3)
                <*> pure False

      unconsConstant :: Char -> Text -> Maybe Text
      unconsConstant c t = do
        (ht, tt) <- uncons t
        guard (ht == c)
        pure tt

      hush :: Either a b -> Maybe b
      hush = either (const Nothing) Just
  parseJSON _ = mzero

-- For applicability failures
data TermValidationError
  = Required String
  | NotApplicable String
  deriving stock (Eq)

instance Show TermValidationError where
  show (Required s) = "Missing required term: " ++ s
  show (NotApplicable s) = "Term not applicable to contract: " ++ s

data Assertions = Assertions
  { context :: AssertionContext,
    assertions :: [Assertion]
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

newtype RRMOMin = RRMOMin Rational
  deriving newtype (Show, ToOSLType, FromJSON, ToJSON)

newtype RRMOMax = RRMOMax Rational
  deriving newtype (Show, ToOSLType, FromJSON, ToJSON)

data AssertionContext = AssertionContext
  { rrmoMin :: RRMOMin,
    rrmoMax :: RRMOMax
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

newtype ZeroRiskInterest = ZeroRiskInterest Rate
  deriving newtype (Show, FromJSON, ToJSON, ToOSLType)

newtype ExpectedNPV = ExpectedNPV Actus.Domain.Basic.Value
  deriving newtype (Show, FromJSON, ToJSON, ToOSLType)

data Assertion = NpvAssertionAgainstZeroRiskBond
  { zeroRiskInterest :: ZeroRiskInterest,
    expectedNpv :: ExpectedNPV
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Reference type
data ReferenceType
  = -- | Contract
    CNT
  | -- | Contract Identifier
    CID
  | -- | Market Object Identifier
    MOC
  | -- | Legal Entity Identifier
    EID
  | -- | Contract Structure
    CST
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | Reference role
data ReferenceRole
  = -- | Underlying
    UDL
  | -- | First Leg
    FIL
  | -- | Second Leg
    SEL
  | -- | Convered Contract
    COVE
  | -- | Covering Contract
    COVI
  deriving stock (Eq, Read, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

newtype MarketObjectCode = MarketObjectCode String
  deriving newtype (Show, FromJSON, ToJSON, ToOSLType)

newtype ContractIdentifier = ContractIdentifier String
  deriving newtype (Show, FromJSON, ToJSON, ToOSLType)

-- | Reference object
data Identifier = Identifier
  { marketObjectCode :: Maybe MarketObjectCode,
    contractIdentifier :: Maybe ContractIdentifier
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Reference
  = ReferenceTerms ContractTerms
  | ReferenceId Identifier
  deriving stock (Show, Generic)
  deriving anyclass (ToJSON)

-- | Contract structure
data ContractStructure = ContractStructure
  { reference :: Reference,
    referenceType :: ReferenceType,
    referenceRole :: ReferenceRole
  }
  deriving stock (Show, Generic)

instance ToJSON ContractStructure where
  toJSON ContractStructure {..} =
    object
      [ "object" .= toJSON reference,
        "referenceType" .= toJSON referenceType,
        "referenceRole" .= toJSON referenceRole
      ]

getMarketObjectCode :: Reference -> Maybe MarketObjectCode
getMarketObjectCode (ReferenceId i) = marketObjectCode i
getMarketObjectCode (ReferenceTerms t) = marketObjectCodeRef t

getContractIdentifier :: Reference -> Maybe ContractIdentifier
getContractIdentifier (ReferenceId i) = contractIdentifier i
getContractIdentifier (ReferenceTerms ContractTerms {..}) = Just contractId

newtype COCE = COCE Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype FeeRate = FeeRate Rate
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype InterestAccrued = InterestAccrued Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype IPCBA = IPBCA Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NominalRate = NominalRate Rate
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NominalRate2 = NominalRate2 Rate
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype ISM = ISM Rate
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NotionalPrincipal = NotionalPrincipal Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype PremiumDiscountAtIED = PremiumDiscountAtIED Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NextPrincipalRedemptionPayment = NextPrincipalRedemptionPayment Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype PriceAtPurchaseDate = PriceAtPurchaseDate Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype PriceAtTerminationDate = PriceAtTerminationDate Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype ScalingIndexAtContractDealDate = ScalingIndexAtContractDealDate Rational -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype ScalingIndexAtStatusDate = ScalingIndexAtStatusDate Rational -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NotionalScalingMultiplier = NotionalScalingMultiplier Rate
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype Quantity = Quantity Rational -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype OptionStrike1 = OptionStrike1 Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype ExerciseAmount = ExerciseAmount Quantity
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype FuturesPrice = FuturesPrice Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype PenaltyRate = PenaltyRate Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NextResetRate = NextResetRate Rate
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype RateSpread = RateSpread Rational -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype RateMultiplier = RateMultiplier Rational
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype PeriodFloor = PeriodFloor Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype PeriodCap = PeriodCap Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype LifeCap = LifeCap Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype LifeFloor = LifeFloor Actus.Domain.Basic.Value -- TODO: is this right?
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype MarketObjectCodeOfRateReset = MarketObjectCodeOfRateReset String
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

newtype NextDividendPaymentAmount = NextDividendPaymentAmount Actus.Domain.Basic.Value
  deriving newtype (Read, Show, FromJSON, ToJSON, ToOSLType)

-- | ACTUS contract terms and attributes are defined in
--    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-terms.json
data ContractTerms = ContractTerms
  { -- General
    contractId :: ContractIdentifier,
    contractType :: CT,
    -- TODO: contractStructure cannot be here because OSL can't
    -- (straightforwardly) handle mutually recursive data types
    -- , contractStructure                        :: [ContractStructure]
    contractRole :: CR,
    settlementCurrency :: Maybe String,
    -- Calendar

    -- | Initial Exchange Date
    initialExchangeDate :: Maybe LocalTime,
    -- | Day Count Convention
    dayCountConvention :: Maybe DCC,
    scheduleConfig :: ScheduleConfig,
    -- Contract Identification

    -- | Status Date
    statusDate :: LocalTime,
    -- | Market Object Code
    marketObjectCodeRef :: Maybe MarketObjectCode,
    -- Counterparty

    -- | Contract Performance
    contractPerformance :: Maybe PRF',
    -- | Credit Event Type Covered
    creditEventTypeCovered :: Maybe CETC,
    -- | Coverage Of Credit Enhancement
    coverageOfCreditEnhancement :: Maybe COCE,
    -- | Guaranteed Exposure
    guaranteedExposure :: Maybe CEGE,
    -- Fees

    -- | Cycle Of Fee
    cycleOfFee :: Maybe Cycle,
    -- | Cycle Anchor Date Of Fee
    cycleAnchorDateOfFee :: Maybe LocalTime,
    -- | Fee Accrued
    feeAccrued :: Maybe FEAC,
    -- | Fee Basis
    feeBasis :: Maybe FEB,
    -- | Fee Rate
    feeRate :: Maybe FeeRate,
    -- Interest

    -- | Cycle Anchor Date Of Interest Payment
    cycleAnchorDateOfInterestPayment :: Maybe LocalTime,
    -- | Cycle Of Interest Payment
    cycleOfInterestPayment :: Maybe Cycle,
    -- | Accrued Interest
    accruedInterest :: Maybe InterestAccrued,
    -- | Capitalization End Date
    capitalizationEndDate :: Maybe LocalTime,
    -- | Cycle Anchor Date Of Interest Calculation Base
    cycleAnchorDateOfInterestCalculationBase :: Maybe LocalTime,
    -- | Cycle Of Interest Calculation Base
    cycleOfInterestCalculationBase :: Maybe Cycle,
    -- | Interest Calculation Base
    interestCalculationBase :: Maybe IPCB',
    -- | Interest Calculation Base Amount
    interestCalculationBaseA :: Maybe IPCBA,
    -- | Nominal Interest Rate
    nominalInterestRate :: Maybe NominalRate,
    -- | Nominal Interest Rate (Second Leg in Plain Vanilla Swap)
    nominalInterestRate2 :: Maybe NominalRate2,
    -- | Interest Scaling Multiplier
    interestScalingMultiplier :: Maybe ISM,
    -- Dates

    -- | Maturity Date
    maturityDate :: Maybe LocalTime,
    -- | Amortization Date
    amortizationDate :: Maybe LocalTime,
    -- | Exercise Date
    exerciseDate :: Maybe LocalTime,
    -- Notional Principal

    -- | Notional Principal
    notionalPrincipal :: Maybe NotionalPrincipal,
    -- | Premium Discount At IED
    premiumDiscountAtIED :: Maybe PremiumDiscountAtIED,
    -- | Cycle Anchor Date Of Principal Redemption
    cycleAnchorDateOfPrincipalRedemption :: Maybe LocalTime,
    -- | Cycle Of Principal Redemption
    cycleOfPrincipalRedemption :: Maybe Cycle,
    -- | Next Principal Redemption Payment
    nextPrincipalRedemptionPayment :: Maybe NextPrincipalRedemptionPayment,
    -- | Purchase Date
    purchaseDate :: Maybe LocalTime,
    -- | Price At Purchase Date
    priceAtPurchaseDate :: Maybe PriceAtPurchaseDate,
    -- | Termination Date
    terminationDate :: Maybe LocalTime,
    -- | Price At Termination Date
    priceAtTerminationDate :: Maybe PriceAtTerminationDate,
    -- | Quantity
    quantity :: Maybe Quantity,
    -- | The currency of the cash flows
    currency :: Maybe String,
    -- | The currency of the cash flows of the second leg
    currency2 :: Maybe String,
    -- Scaling Index

    -- | Scaling Index At Status Date
    scalingIndexAtStatusDate :: Maybe ScalingIndexAtStatusDate,
    -- | Cycle Anchor Date Of Scaling Index
    cycleAnchorDateOfScalingIndex :: Maybe LocalTime,
    -- | Cycle Of Scaling Index
    cycleOfScalingIndex :: Maybe Cycle,
    -- | Scaling Effect
    scalingEffect :: Maybe SCEF,
    -- | Scaling Index At Contract Deal Date
    scalingIndexAtContractDealDate :: Maybe ScalingIndexAtContractDealDate,
    -- | Market Object Code Of Scaling Index
    marketObjectCodeOfScalingIndex :: Maybe String,
    -- | Notional Scaling Multiplier
    notionalScalingMultiplier :: Maybe NotionalScalingMultiplier,
    -- Optionality

    -- | Cycle Of Optionality
    cycleOfOptionality :: Maybe Cycle,
    -- | Cycle Anchor Date Of Optionality
    cycleAnchorDateOfOptionality :: Maybe LocalTime,
    -- | Option Type
    optionType :: Maybe OPTP,
    -- | Option Strike 1
    optionStrike1 :: Maybe OptionStrike1,
    -- | Option Exercise Type
    optionExerciseType :: Maybe OPXT,
    -- Settlement

    -- | Settlement Period
    settlementPeriod :: Maybe Cycle,
    -- | Delivery Settlement
    deliverySettlement :: Maybe DS,
    -- | Exercise Amount
    exerciseAmount :: Maybe ExerciseAmount,
    -- | Futures Price
    futuresPrice :: Maybe FuturesPrice,
    -- Penalty

    -- | Penalty Rate
    penaltyRate :: Maybe PenaltyRate,
    -- | Penalty Type
    penaltyType :: Maybe PYTP,
    -- | Prepayment Effect
    prepaymentEffect :: Maybe PPEF,
    -- Rate Reset

    -- | Cycle Of Rate Reset
    cycleOfRateReset :: Maybe Cycle,
    -- | Cycle Anchor Date Of Rate Reset
    cycleAnchorDateOfRateReset :: Maybe LocalTime,
    -- | Next Reset Rate
    nextResetRate :: Maybe NextResetRate,
    -- | Rate Spread
    rateSpread :: Maybe RateSpread,
    -- | Rate Multiplier
    rateMultiplier :: Maybe RateMultiplier,
    -- | Period Floor
    periodFloor :: Maybe PeriodFloor,
    -- | Period Cap
    periodCap :: Maybe PeriodCap,
    -- | Life Cap
    lifeCap :: Maybe LifeCap,
    -- | Life Floor
    lifeFloor :: Maybe LifeFloor,
    -- | Market Object Code Of Rate Reset
    marketObjectCodeOfRateReset :: Maybe MarketObjectCodeOfRateReset,
    -- Dividend

    -- | Cycle Of Dividend
    cycleOfDividend :: Maybe Cycle,
    -- | Cycle Anchor Date Of Dividend
    cycleAnchorDateOfDividend :: Maybe LocalTime,
    -- | Next Dividend Payment Amount
    nextDividendPaymentAmount :: Maybe NextDividendPaymentAmount,
    -- | Enable settlement currency
    enableSettlement :: Bool,
    -- | Assertions
    constraints :: Maybe Assertions
  }
  deriving stock (Show, Generic)
  deriving anyclass (ToJSON)

instance FromJSON Reference where
  parseJSON = genericParseJSON defaultOptions {sumEncoding = UntaggedValue}

instance FromJSON ContractStructure where
  parseJSON (Object v) =
    ContractStructure
      <$> v .: "object"
      <*> v .: "referenceType"
      <*> v .: "referenceRole"
  parseJSON _ = mzero

instance FromJSON ContractTerms where
  parseJSON (Object v) =
    ContractTerms
      <$> (v .: "contractID" <|> v .: "contractId")
      <*> v .: "contractType"
      -- <*> (v .: "contractStructure" <|> pure [])
      <*> (v .: "contractRole" <|> pure CR_RPA) -- SWAPS tests miss contractRole in contract terms
      <*> v .:? "settlementCurrency"
      <*> v .:? "initialExchangeDate"
      <*> v .:? "dayCountConvention"
      <*> ( v .: "scheduleConfig"
              <|> ScheduleConfig
                <$> (v .: "calendar" <|> pure (Just CLDR_NC))
                <*> (v .: "endOfMonthConvention" <|> pure (Just EOMC_SD))
                <*> (v .: "businessDayConvention" <|> pure (Just BDC_NULL))
          )
      <*> v .: "statusDate"
      <*> v .:? "marketObjectCode"
      <*> v .:? "contractPerformance"
      <*> v .:? "creditEventTypeCovered"
      <*> v .!? "coverageOfCreditEnhancement"
      <*> v .!? "guaranteedExposure"
      <*> v .:? "cycleOfFee"
      <*> v .:? "cycleAnchorDateOfFee"
      <*> v .:? "feeAccrued"
      <*> v .:? "feeBasis"
      <*> v .!? "feeRate"
      <*> v .:? "cycleAnchorDateOfInterestPayment"
      <*> v .:? "cycleOfInterestPayment"
      <*> v .!? "accruedInterest"
      <*> v .:? "capitalizationEndDate"
      <*> v .:? "cycleAnchorDateOfInterestCalculationBase"
      <*> v .:? "cycleOfInterestCalculationBase"
      <*> v .:? "interestCalculationBase"
      <*> v .!? "interestCalculationBaseAmount"
      <*> v .!? "nominalInterestRate"
      <*> v .!? "nominalInterestRate2"
      <*> v .!? "interestScalingMultiplier"
      <*> v .:? "maturityDate"
      <*> v .:? "amortizationDate"
      <*> v .:? "exerciseDate"
      <*> v .!? "notionalPrincipal"
      <*> v .!? "premiumDiscountAtIED"
      <*> v .:? "cycleAnchorDateOfPrincipalRedemption"
      <*> v .:? "cycleOfPrincipalRedemption"
      <*> v .!? "nextPrincipalRedemptionPayment"
      <*> v .:? "purchaseDate"
      <*> v .!? "priceAtPurchaseDate"
      <*> v .:? "terminationDate"
      <*> v .!? "priceAtTerminationDate"
      <*> v .!? "quantity"
      <*> v .!? "currency"
      <*> v .!? "currency2"
      <*> v .:? "scalingIndexAtStatusDate"
      <*> v .:? "cycleAnchorDateOfScalingIndex"
      <*> v .:? "cycleOfScalingIndex"
      <*> v .:? "scalingEffect"
      <*> v .!? "scalingIndexAtContractDealDate"
      <*> v .:? "marketObjectCodeOfScalingIndex"
      <*> v .!? "notionalScalingMultiplier"
      <*> v .:? "cycleOfOptionality"
      <*> v .:? "cycleAnchorDateOfOptionality"
      <*> v .:? "optionType"
      <*> v .!? "optionStrike1"
      <*> v .:? "optionExerciseType"
      <*> v .:? "settlementPeriod"
      <*> v .:? "deliverySettlement"
      <*> v .!? "exerciseAmount"
      <*> v .!? "futuresPrice"
      <*> v .:? "penaltyRate"
      <*> v .:? "penaltyType"
      <*> v .:? "prepaymentEffect"
      <*> v .:? "cycleOfRateReset"
      <*> v .:? "cycleAnchorDateOfRateReset"
      <*> v .!? "nextResetRate"
      <*> v .!? "rateSpread"
      <*> v .!? "rateMultiplier"
      <*> v .:? "periodFloor"
      <*> v .:? "periodCap"
      <*> v .:? "lifeCap"
      <*> v .:? "lifeFloor"
      <*> v .:? "marketObjectCodeOfRateReset"
      <*> v .:? "cycleOfDividendPayment"
      <*> v .:? "cycleAnchorDateOfDividendPayment"
      <*> v .:? "nextDividendPaymentAmount"
      <*> (fromMaybe False <$> (v .:? "enableSettlement"))
      <*> v .:? "constraints"
    where
      (.!?) :: FromJSON a => Object -> Key -> Parser (Maybe a)
      (.!?) = (.:?)
  -- TODO: why this?
  -- (.!?) w s = w .:? s <|> (fmap read' <$> w .:? s)
  -- read' = fromMaybe (fail "could not Read") . readMay
  parseJSON _ = mzero
