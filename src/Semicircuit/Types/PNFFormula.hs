{-# LANGUAGE DeriveGeneric #-}

module Semicircuit.Types.PNFFormula
  ( Formula (..),
    Quantifiers (Quantifiers),
    ExistentialQuantifier (..),
    UniversalQuantifier (All),
  )
where

import GHC.Generics (Generic)
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Sigma11 (Bound, ExistentialQuantifier (..), Name)

data Formula = Formula
  { qfFormula :: QF.Formula,
    quantifiers :: Quantifiers
  }
  deriving Generic

data Quantifiers = Quantifiers
  { existentialQuantifiers :: [ExistentialQuantifier],
    universalQuantifiers :: [UniversalQuantifier]
  }
  deriving (Eq, Generic)

instance Semigroup Quantifiers where
  (Quantifiers a b) <> (Quantifiers a' b') =
    Quantifiers (a <> a') (b <> b')

instance Monoid Quantifiers where
  mempty = Quantifiers [] []

data UniversalQuantifier =
  All
  { name :: Name
  , bound :: Bound
  }
  deriving (Eq, Generic)
