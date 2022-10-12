module Semicircuit.ToLogicCircuit
  ( semicircuitToLogicCircuit
  ) where


import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.FiniteField (FiniteField)
import OSL.Types.ErrorMessage (ErrorMessage)
import Semicircuit.Types.Semicircuit (Semicircuit)


semicircuitToLogicCircuit
  :: ann
  -> FiniteField
  -> Semicircuit
  -> Either (ErrorMessage ann) LogicCircuit
semicircuitToLogicCircuit = todo


todo :: a
todo = todo
