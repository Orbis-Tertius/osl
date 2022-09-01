{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module OSL.Types.Arity (Arity (..)) where


newtype Arity = Arity { unArity :: Int }
  deriving newtype (Eq, Ord, Num, Show)
