{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Semicircuit.Types.PNFFormula
  ( Formula (..)
  , Quantifiers (..)
  , ExistentialQuantifier (..)
  , UniversalQuantifier (..)
  ) where


import Semicircuit.Types.Sigma11 (Bound, Name, ExistentialQuantifier (..))
import qualified Semicircuit.Types.QFFormula as QF


data Formula =
  Formula
  { qfFormula :: QF.Formula
  , quantifiers :: Quantifiers
  }


data Quantifiers =
  Quantifiers
  { existentialQuantifiers :: [ExistentialQuantifier]
  , universalQuantifiers :: [UniversalQuantifier]
  }
  deriving Eq

instance Semigroup Quantifiers where
  (Quantifiers a b) <> (Quantifiers a' b') =
    Quantifiers (a <> a') (b <> b')

instance Monoid Quantifiers where
  mempty = Quantifiers [] []


data UniversalQuantifier = All Name Bound
  deriving Eq
