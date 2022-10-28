{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}

module Semicircuit.Types.PNFFormula
  ( Formula (..),
    Quantifiers (Quantifiers),
    ExistentialQuantifier (..),
    UniversalQuantifier (All),
  )
where

import Control.Lens ((^.))
import Data.List (intercalate)
import GHC.Generics (Generic)
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Sigma11 (Bound, ExistentialQuantifier (..), Name)

data Formula = Formula
  { qfFormula :: QF.Formula,
    quantifiers :: Quantifiers
  }
  deriving (Generic)

instance Show Formula where
  show f = show (f ^. #quantifiers) <> ", " <> show (f ^. #qfFormula)

data Quantifiers = Quantifiers
  { existentialQuantifiers :: [ExistentialQuantifier],
    universalQuantifiers :: [UniversalQuantifier]
  }
  deriving (Eq, Generic)

instance Show Quantifiers where
  show qs =
    intercalate
      ", "
      (("∃" <>) . show <$> (qs ^. #existentialQuantifiers))
      <> ", "
      <> intercalate ", " (("∀" <>) . show <$> (qs ^. #universalQuantifiers))

instance Semigroup Quantifiers where
  (Quantifiers a b) <> (Quantifiers a' b') =
    Quantifiers (a <> a') (b <> b')

instance Monoid Quantifiers where
  mempty = Quantifiers [] []

data UniversalQuantifier = All
  { name :: Name,
    bound :: Bound
  }
  deriving (Eq, Generic)

instance Show UniversalQuantifier where
  show q = "all " <> show (q ^. #name) <> "<" <> show (q ^. #bound)
