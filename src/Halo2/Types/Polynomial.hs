{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.Polynomial (Polynomial (Polynomial)) where

import Data.List (intercalate)
import qualified Data.Map as Map
import Halo2.Prelude
import Halo2.Types.Coefficient (Coefficient)
import Halo2.Types.PowerProduct (PowerProduct)

newtype Polynomial = Polynomial {monos :: Map PowerProduct Coefficient}
  deriving (Eq, Ord, Generic)

instance Show Polynomial where
  show xs =
    intercalate
      " + "
      ( (\(p, c) -> show c <> show p)
          <$> Map.toList (monos xs)
      )
