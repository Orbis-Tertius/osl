{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Semicircuit.Types.PNFFormula
  ( Formula (..)
  , Quantifiers (..)
  , FOExistsQ (..)
  , NumPrecUniQs (..)
  , FOUniQ (..)
  , SOExistsQ (..)
  ) where


import Data.List.NonEmpty (NonEmpty)

import OSL.Types.Cardinality (Cardinality)
import OSL.Types.Sigma11 (Bound)
import qualified Semicircuit.Types.QFFormula as QF


data Formula =
  Formula
  { qfFormula :: QF.Formula
  , quantifiers :: Quantifiers
  }


data Quantifiers =
  Quantifiers
  { foExistentialQuantifiers :: [FOExistsQ]
  , foUniversalQuantifiers :: [FOUniQ]
  , soQuantifiers :: [SOExistsQ]
  }

instance Semigroup Quantifiers where
  (Quantifiers a b c) <> (Quantifiers a' b' c') =
    Quantifiers (a <> a') (b <> b') (c <> c')

instance Monoid Quantifiers where
  mempty = Quantifiers [] [] []


data FOExistsQ = Exists Bound NumPrecUniQs


newtype NumPrecUniQs = NumPrecUniQs Int
  deriving Num


data FOUniQ = ForAll Bound


data SOExistsQ =
    ExistsF Cardinality Bound (NonEmpty Bound)
  | ExistsP Cardinality Bound Bound
