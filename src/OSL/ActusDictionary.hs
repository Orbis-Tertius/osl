{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module OSL.ActusDictionary (actusDictionary, actusNameList, actusDictionaryFormatted) where

import Actus.Domain.BusinessEvents (EventType (..))
import Actus.Domain.ContractState (ContractState, Numerator, Denominator, Rational, Value, Rate, Period, MD', NT, IPNR, IPAC, IPAC1, IPAC2, IPLA, FEAC, NSC, ISC, SD, PRNXT, IPCB, XD, XA)
import Actus.Domain.ContractTerms (PRF')
import Control.Monad.State (State, execState)
import Data.Proxy (Proxy (Proxy))
import Data.Time (LocalTime (..), TimeOfDay (..))
import OSL.Format (formatContext)
import OSL.FromHaskell (AddToOSLContext, addToOSLContextM, mkDataToAddOSL, Newtype)
import OSL.Types.OSL (ValidContext, ContextType (Global), Name)
import Prelude hiding (Rational)

mkDataToAddOSL "EventType"
mkDataToAddOSL "ContractState"

actusDictionaryFormatted :: String
actusDictionaryFormatted = formatContext actusDictionary actusNameList

actusDictionary :: ValidContext Global ()
actusDictionary = flip execState mempty $ do
  add (Proxy @TimeOfDay)
  add (Proxy @LocalTime)
  add (Proxy @EventType)
  add (Proxy @(Newtype PRF'))
  add (Proxy @(Newtype Numerator))
  add (Proxy @(Newtype Denominator))
  add (Proxy @(Newtype Rational))
  add (Proxy @(Newtype Value))
  add (Proxy @(Newtype Rate))
  add (Proxy @(Newtype Period))
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
  where
    add :: forall a. AddToOSLContext a => Proxy a -> State (ValidContext Global ()) ()
    add = addToOSLContextM

actusNameList :: [Name]
actusNameList =
  [ "TimeOfDay"
  , "LocalTime"
  , "IED"
  , "FP"
  , "PR" 
  , "PD" 
  , "PY" 
  , "PP" 
  , "IP" 
  , "IPFX"
  , "IPFL"
  , "IPCI"
  , "CE"
  , "RRF" 
  , "RR"
  , "PRF"
  , "DV"
  , "PRD"
  , "MR"
  , "TD"
  , "SC"
  , "IPCB"
  , "MD"
  , "XD"
  , "STD"
  , "PI"
  , "AD"
  , "EventType"
  , "PRF'"
  , "Numerator"
  , "Denominator"
  , "Rational"
  , "Value"
  , "Rate"
  , "Period"
  , "MD'"
  , "NT"
  , "IPNR"
  , "IPAC"
  , "IPAC1"
  , "IPAC2"
  , "IPLA"
  , "FEAC"
  , "NSC"
  , "ISC"
  , "SD"
  , "PRNXT"
  , "IPCB"
  , "XD"
  , "XA"
  , "ContractState"
  ]
