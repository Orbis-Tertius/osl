{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Semicircuit.Types.Semicircuit
  ( Semicircuit (Semicircuit),
    FreeVariables (..),
  )
where

import Data.Set (Set)
import GHC.Generics (Generic)
import Semicircuit.Types.PNFFormula (Formula)
import Semicircuit.Types.Sigma11 (Name)

data Semicircuit = Semicircuit
  { freeVariables :: FreeVariables,
    formula :: Formula
  }
  deriving (Generic, Show)

newtype FreeVariables = FreeVariables {unFreeVariables :: Set Name}
  deriving (Generic, Show)
