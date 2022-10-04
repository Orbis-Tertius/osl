module Semicircuit.Types.PNFFormula
  ( PNFFormula (..)
  , Quantifiers (..)
  , FOExistsQ (..)
  , NumPrecUniQs (..)
  , FOUniQ (..)
  , SOExistsQ (..)
  ) where


import Data.List.NonEmpty (NonEmpty)

import OSL.Types.Cardinality (Cardinality)
import OSL.Types.Sigma11 (Bound)
import Semicircuit.Types.QFFormula (QFFormula)


data PNFFormula =
  PNFFormula
  { qfFormula :: QFFormula
  , quantifiers :: Quantifiers
  }


data Quantifiers =
  Quantifiers
  { foExistentialQuantifiers :: [FOExistsQ]
  , foUniversalQuantifiers :: [FOUniQ]
  , soQuantifiers :: [SOExistsQ]
  }


data FOExistsQ = Exists Bound NumPrecUniQs


newtype NumPrecUniQs = NumPrecUniQs Int


data FOUniQ = ForAll Bound


data SOExistsQ =
    ExistsF Cardinality Bound (NonEmpty Bound)
  | ExistsP Cardinality Bound Bound
