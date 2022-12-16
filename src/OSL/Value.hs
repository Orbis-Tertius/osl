{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Value (fstOfPair, sndOfPair, defaultValue) where

import Control.Lens ((^.))
import qualified Data.Map as Map
import OSL.Type (dropTypeAnnotations)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import qualified OSL.Types.OSL as OSL
import OSL.Types.Value (Value (Pair', Bool, Fun, Nat, Int, Fp', Fin', Iota1', Maybe'', List'', Map'', To'))
import Stark.Types.Scalar (zero)

fstOfPair, sndOfPair :: Value -> Either (ErrorMessage ()) Value
fstOfPair (Pair' x _) = pure x
fstOfPair _ = Left . ErrorMessage () $
  "fstOfPair: expected a pair"
sndOfPair (Pair' _ y) = pure y
sndOfPair _ = Left . ErrorMessage () $
  "sndOfPair: expected a pair"

defaultValue ::
  OSL.ValidContext t ann ->
  OSL.Type () ->
  Either (ErrorMessage ()) Value
defaultValue c =
  \case
    OSL.NamedType ann name ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data a) ->
          To' name <$> rec (dropTypeAnnotations a)
        _ -> Left (ErrorMessage ann "expected the name of a type")
    OSL.Prop _ -> pure (Bool False)
    OSL.F {} -> pure (Fun mempty)
    OSL.P {} -> pure (Fun mempty)
    OSL.N _ -> pure (Nat zero)
    OSL.Fin ann 0 -> Left (ErrorMessage ann "Fin(0) has no default value; it is uninhabited")
    OSL.Fin {} -> pure (Fin' zero)
    OSL.Fp _ -> pure (Fp' zero)
    OSL.Z _ -> pure (Int zero)
    OSL.Product _ a b ->
      Pair' <$> rec a <*> rec b
    OSL.Coproduct _ a _ ->
      Iota1' <$> rec a
    OSL.Maybe {} -> pure (Maybe'' Nothing)
    OSL.List {} -> pure (List'' mempty)
    OSL.Map {} -> pure (Map'' mempty)
  where
    rec = defaultValue c
