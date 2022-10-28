{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.EqualityConstraints
  ( EqualityConstraints (EqualityConstraints, getEqualityConstraints),
  )
where

import Data.List (intercalate)
import Halo2.Prelude
import Halo2.Types.EqualityConstraint

newtype EqualityConstraints = EqualityConstraints
  {getEqualityConstraints :: [EqualityConstraint]}
  deriving (Eq, Ord, Generic, Semigroup, Monoid)

instance Show EqualityConstraints where
  show (EqualityConstraints xs) =
    "{" <> intercalate ", " (show <$> xs) <> "}"
