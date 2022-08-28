{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module OSL.Types.Arity (Arity (..)) where


newtype Arity = Arity { unArity :: Int }
  deriving (Eq, Ord, Num, Show)
