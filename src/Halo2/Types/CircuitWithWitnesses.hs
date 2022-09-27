{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.CircuitWithWitnesses ( CircuitWithWitnesses (CircuitWithWitnesses) ) where


import           Halo2.Prelude
import           Halo2.Types.Circuit                  (Circuit)
import           Halo2.Types.Witness                  (Witness)
import           Halo2.Types.WitnessColumns           (WitnessColumns)
import           Halo2.Types.WitnessGenerationContext (WitnessGenerationContext)


-- A witness is the subset of the advice columns which are computed
-- from the values of the instance columns (the public inputs)
-- and the values of the other advice columns (the private inputs)
-- which are provided as input to the zkSNARK proving process.
-- A circuit with witnesses specifies a circuit and which columns
-- constitute the witness and what function computes the witness.
data CircuitWithWitnesses =
  CircuitWithWitnesses
  { circuit        :: Circuit
  , witnessColumns :: WitnessColumns
  , witnesses      :: WitnessGenerationContext -> Witness
  }
  deriving Generic
