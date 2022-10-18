{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Arity (Arity (..)) where

import GHC.Generics (Generic)

newtype Arity = Arity {unArity :: Int}
  deriving newtype (Eq, Ord, Num, Show)
  deriving stock Generic
