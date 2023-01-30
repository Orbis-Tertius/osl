{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-orphans #-}

module Actus.Domain.Basic where

import Data.Aeson (FromJSON, ToJSON)
import Data.Time (TimeOfDay, LocalTime)
import GHC.Generics (Generic)
import OSL.FromHaskell (ToOSLType (..), mkDataToAddOSL)
import Prelude hiding (Rational)

newtype Numerator = Numerator Integer
  deriving newtype (Read, Show, Eq, ToOSLType, FromJSON, ToJSON)

newtype Denominator = Denominator Integer
  deriving newtype (Read, Show, Eq, ToOSLType, FromJSON, ToJSON)

data Rational = Rational Numerator Denominator
  deriving (Read, Show, Eq, Generic)

instance FromJSON Rational
instance ToJSON Rational

mkDataToAddOSL "Rational"
mkDataToAddOSL "TimeOfDay"
mkDataToAddOSL "LocalTime"

newtype Value = Value Integer
  deriving newtype (Read, Show, Eq, ToOSLType, FromJSON, ToJSON)

newtype Rate = Rate Rational
  deriving newtype (Read, Show, Eq, ToOSLType, FromJSON, ToJSON)

-- Fee accrued
newtype FEAC = FEAC Value
  deriving newtype (Read, Show, Eq, ToOSLType, FromJSON, ToJSON)
