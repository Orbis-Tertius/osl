{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.DeBruijnIndex (DeBruijnIndex (..)) where

newtype DeBruijnIndex = DeBruijnIndex {unDeBruijnIndex :: Int}
  deriving newtype (Eq, Ord, Num, Show)
