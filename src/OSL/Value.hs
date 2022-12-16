{-# LANGUAGE OverloadedStrings #-}

module OSL.Value (fstOfPair, sndOfPair) where

import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.Value (Value (Pair'))

fstOfPair, sndOfPair :: Value -> Either (ErrorMessage ()) Value
fstOfPair (Pair' x _) = pure x
fstOfPair _ = Left . ErrorMessage () $
  "fstOfPair: expected a pair"
sndOfPair (Pair' _ y) = pure y
sndOfPair _ = Left . ErrorMessage () $
  "sndOfPair: expected a pair"
