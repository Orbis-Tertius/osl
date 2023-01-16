{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Halo2.Types.Argument
  ( Argument (Argument),
    Statement (Statement),
    Witness (Witness),
  )
where

import Data.Map (Map)
import GHC.Generics (Generic)
import Halo2.Types.CellReference (CellReference)
import Stark.Types.Scalar (Scalar)

data Argument = Argument
  { statement :: Statement,
    witness :: Witness
  }
  deriving (Generic, Show)

instance Semigroup Argument where
  Argument s0 w0 <> Argument s1 w1 =
    Argument (s0 <> s1) (w0 <> w1)

instance Monoid Argument where
  mempty = Argument mempty mempty

newtype Statement = Statement {unStatement :: Map CellReference Scalar}
  deriving (Generic, Semigroup, Monoid, Show)

newtype Witness = Witness {unWitness :: Map CellReference Scalar}
  deriving (Generic, Semigroup, Monoid, Show)
