{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OSL.Types.Cardinality (Cardinality (..)) where

-- The maximum number of elements of a collection type.
newtype Cardinality = Cardinality Integer
  deriving newtype (Eq, Ord, Show, Num)
