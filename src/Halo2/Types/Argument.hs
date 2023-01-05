{-# LANGUAGE DeriveGeneric #-}

module Halo2.Types.Argument
  ( Argument (Argument),
    Statement (Statement),
    Witness (Witness),
  ) where

import Data.Map (Map)
import GHC.Generics (Generic)
import Halo2.Types.CellReference (CellReference)
import Stark.Types.Scalar (Scalar)

data Argument =
  Argument
  { statement :: Statement,
    witness :: Witness
  }
  deriving Generic

newtype Statement = Statement { unStatement :: Map CellReference Scalar }
  deriving Generic

newtype Witness = Witness { unWitness :: Map CellReference Scalar }
  deriving Generic
