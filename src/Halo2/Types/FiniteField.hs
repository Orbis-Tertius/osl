{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-identities #-}

module Halo2.Types.FiniteField (FiniteField (FiniteField)) where

import Halo2.Prelude

newtype FiniteField = FiniteField {order :: Integer}
  deriving (Num, Enum, Real, Integral, Eq, Ord, Show, Generic)
