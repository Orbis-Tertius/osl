module Semicircuit.Translation
  ( semicircuitToLogicCircuit
  ) where


import Halo2.Types.Circuit (LogicCircuit)
import OSL.Types.ErrorMessage (ErrorMessage)
import Semicircuit.Types.Semicircuit (Semicircuit)


semicircuitToLogicCircuit
  :: ann
  -> Semicircuit
  -> Either (ErrorMessage ann) LogicCircuit
semicircuitToLogicCircuit = todo


todo :: a
todo = todo
