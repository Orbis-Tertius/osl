{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module OSL.Types.DeBruijnIndex (DeBruijnIndex (..)) where


newtype DeBruijnIndex = DeBruijnIndex { unDeBruijnIndex :: Int }
  deriving (Eq, Ord, Num, Show)
