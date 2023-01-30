{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Actus.Domain.Basic where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import OSL.FromHaskell (ToOSLType (..), mkDataToAddOSL)
import Prelude hiding (Rational)

newtype Numerator = Numerator Integer
  deriving newtype (Show, Eq, ToOSLType, FromJSON, ToJSON)

newtype Denominator = Denominator Integer
  deriving newtype (Show, Eq, ToOSLType, FromJSON, ToJSON)

data Rational = Rational Numerator Denominator
  deriving (Show, Eq, Generic)

instance FromJSON Rational
instance ToJSON Rational

mkDataToAddOSL "Rational"
