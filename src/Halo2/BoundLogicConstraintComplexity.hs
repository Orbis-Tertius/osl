{-# LANGUAGE DeriveGeneric #-}


module Halo2.BoundLogicConstraintComplexity
  ( ComplexityBound (ComplexityBound)
  , boundLogicConstraintComplexity
  ) where


import GHC.Generics (Generic)
import Halo2.Types.Circuit (LogicCircuit)


newtype ComplexityBound = ComplexityBound { unComplexityBound :: Int }
  deriving Generic


boundLogicConstraintComplexity
  :: ComplexityBound
  -> LogicCircuit
  -> LogicCircuit
boundLogicConstraintComplexity = todo


todo :: a
todo = todo
