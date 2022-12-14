{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Witness
  ( splitWitness
  ) where

import OSL.Types.Argument (Witness (Witness))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.Value (Value (Pair', Fin'))

splitWitness :: ann -> Witness -> Either (ErrorMessage ann) (Witness, Witness)
splitWitness ann =
  \case
    Witness (Pair' w0 w1) -> pure (Witness w0, Witness w1)
    Witness (Fin' 0) -> pure (Witness (Fin' 0), Witness (Fin' 0))
    _ -> Left . ErrorMessage ann $ "splitWitness: expected a pair"
