{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Semicircuit.Types.PNFFormula
  ( Formula (..)
  , Quantifiers (..)
  , ExistentialQuantifier (..)
  , UniversalQuantifier (..)
  ) where


import OSL.Types.Cardinality (Cardinality)
import Semicircuit.Types.Sigma11 (Bound, InputBound, OutputBound, Name)
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


data ExistentialQuantifier =
    Some Name Cardinality [InputBound] OutputBound
  | SomeP Name Cardinality InputBound OutputBound
  deriving Eq


data UniversalQuantifier = All Name Bound
  deriving Eq
