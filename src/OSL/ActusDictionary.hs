{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module OSL.ActusDictionary (actusDictionary, actusNameList, actusDictionaryFormatted) where

import Actus.Domain.BusinessEvents (EventType (..))
import Control.Monad.State (execState)
import Data.Proxy (Proxy (Proxy))
import OSL.Format (formatContext)
import OSL.FromHaskell (addToOSLContextM, mkDataToAddOSL)
import OSL.Types.OSL (ValidContext, ContextType (Global), Name)

mkDataToAddOSL "EventType"

actusDictionaryFormatted :: String
actusDictionaryFormatted = formatContext actusDictionary actusNameList

actusDictionary :: ValidContext Global ()
actusDictionary = flip execState mempty $ do
  add (Proxy @EventType)
  where
    add = addToOSLContextM

actusNameList :: [Name]
actusNameList =
  [ "IED"
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
  ]
