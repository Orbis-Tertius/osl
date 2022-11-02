{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLabels #-}

module Semicircuit.Types.PNFFormula
  ( Formula (Formula),
    Quantifiers (Quantifiers),
    ExistentialQuantifier (Some, SomeP),
    UniversalQuantifier (All),
    InstanceQuantifier (Instance),
  )
where

import Control.Lens ((^.))
import Data.List (intercalate)
import GHC.Generics (Generic)
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Sigma11 (Bound, ExistentialQuantifier (..), Name, InputBound, OutputBound)

data Formula = Formula
  { qfFormula :: QF.Formula,
    quantifiers :: Quantifiers
  }
  deriving (Generic)

instance Show Formula where
  show f = show (f ^. #quantifiers) <> ", " <> show (f ^. #qfFormula)

data Quantifiers = Quantifiers
  { existentialQuantifiers :: [ExistentialQuantifier],
    universalQuantifiers :: [UniversalQuantifier],
    instanceQuantifiers :: [InstanceQuantifier]
  }
  deriving (Eq, Generic)

instance Show Quantifiers where
  show qs =
    intercalate
      ", "
      (
         (("λ" <>) . show <$> (qs ^. #instanceQuantifiers))
      <> (("∃" <>) . show <$> (qs ^. #existentialQuantifiers))
      <> (("∀" <>) . show <$> (qs ^. #universalQuantifiers))
      )

instance Semigroup Quantifiers where
  (Quantifiers a b c) <> (Quantifiers a' b' c') =
    Quantifiers (a <> a') (b <> b') (c <> c')

instance Monoid Quantifiers where
  mempty = Quantifiers [] [] []

data UniversalQuantifier = All
  { name :: Name,
    bound :: Bound
  }
  deriving (Eq, Generic)

instance Show UniversalQuantifier where
  show q = show (q ^. #name) <> "<" <> show (q ^. #bound)

data InstanceQuantifier =
  Instance
  { name :: Name
  , inputBounds :: [InputBound]
  , outputBound :: OutputBound
  }
  deriving (Eq, Generic)

instance Show InstanceQuantifier where
  show g = show (g ^. #name) <>
    (if null (g ^. #inputBounds) then ""
     else "(" <> intercalate ", " (show <$> (g ^. #inputBounds)) <> ")")
    <> "<" <> show (g ^. #outputBound)
