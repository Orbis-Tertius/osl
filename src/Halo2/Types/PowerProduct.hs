{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.PowerProduct (PowerProduct (PowerProduct, getPowerProduct)) where

import Data.List (intercalate)
import Data.Map (toList)
import Halo2.Prelude
import Halo2.Types.Exponent (Exponent)
import Halo2.Types.PolynomialVariable (PolynomialVariable)

newtype PowerProduct = PowerProduct {getPowerProduct :: Map PolynomialVariable Exponent}
  deriving (Eq, Ord, Generic)

instance Show PowerProduct where
  show xs = intercalate "*"
    ((\(x,e) -> show x <> "^" <> show e)
     <$> toList (getPowerProduct xs))
