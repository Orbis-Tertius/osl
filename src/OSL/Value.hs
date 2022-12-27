{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module OSL.Value
  ( fstOfPair,
    sndOfPair,
    fstOfPairMay,
    sndOfPairMay,
    coproductIndicator,
    iota1Inverse,
    iota2Inverse,
    maybeIndicator,
    justInverse,
    listLength,
    listFun,
    mapSize,
    mapKeys,
    mapFun,
    toInverse,
    uncurryFun,
    defaultValue,
  )
where

import Cast (intToInteger)
import Control.Lens ((^.))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import OSL.Type (dropTypeAnnotations)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import qualified OSL.Types.OSL as OSL
import OSL.Types.Value (Value (Bool, Fin', Fp', Fun, Int, Iota1', Iota2', List'', Map'', Maybe'', Nat, Pair', To'))
import Stark.Types.Scalar (integerToScalar, one, zero)

fstOfPair, sndOfPair :: Value -> Either (ErrorMessage ()) Value
fstOfPair (Pair' x _) = pure x
fstOfPair _ =
  Left . ErrorMessage () $
    "fstOfPair: expected a pair"
sndOfPair (Pair' _ y) = pure y
sndOfPair _ =
  Left . ErrorMessage () $
    "sndOfPair: expected a pair"

fstOfPairMay, sndOfPairMay :: Value -> Maybe Value
fstOfPairMay (Pair' x _) = pure x
fstOfPairMay _ = Nothing
sndOfPairMay (Pair' _ y) = pure y
sndOfPairMay _ = Nothing

iota1Inverse, iota2Inverse :: Value -> Value -> Maybe Value
iota1Inverse _ (Iota1' x) = pure x
iota1Inverse d (Iota2' _) = pure d
iota1Inverse _ _ = Nothing
iota2Inverse _ (Iota2' x) = pure x
iota2Inverse d (Iota1' _) = pure d
iota2Inverse _ _ = Nothing

coproductIndicator :: Value -> Maybe Value
coproductIndicator (Iota1' _) = pure (Nat zero)
coproductIndicator (Iota2' _) = pure (Nat one)
coproductIndicator _ = Nothing

maybeIndicator :: Value -> Maybe Value
maybeIndicator (Maybe'' Nothing) = pure (Nat zero)
maybeIndicator (Maybe'' (Just _)) = pure (Nat one)
maybeIndicator _ = Nothing

justInverse :: Value -> Value -> Maybe Value
justInverse _ (Maybe'' (Just x)) = pure x
justInverse d (Maybe'' Nothing) = pure d
justInverse _ _ = Nothing

listLength :: Value -> Maybe Value
listLength (List'' xs) = Nat <$> integerToScalar (intToInteger (length xs))
listLength _ = Nothing

listFun :: Value -> Maybe Value
listFun (List'' xs) =
  Fun . Map.fromList
    <$> sequence
      [(,x) . Nat <$> integerToScalar i | (i, x) <- zip [0 ..] xs]
listFun _ = Nothing

mapSize :: Value -> Maybe Value
mapSize (Map'' xs) = Nat <$> integerToScalar (intToInteger (Map.size xs))
mapSize _ = Nothing

mapKeys :: Value -> Maybe Value
mapKeys (Map'' xs) =
  Fun . Map.fromList
    <$> sequence
      [(,x) . Nat <$> integerToScalar i | (i, x) <- zip [0 ..] (Map.keys xs)]
mapKeys _ = Nothing

mapFun :: Value -> Maybe Value
mapFun (Map'' xs) = pure (Fun xs)
mapFun _ = Nothing

toInverse :: Value -> Maybe Value
toInverse (To' _ x) = pure x
toInverse _ = Nothing

uncurryFun :: Map Value Value -> Map Value Value
uncurryFun f =
  Map.fromList . concat . catMaybes $
    [ case g of
        Fun g' -> pure [(Pair' x0 x1, y) | (x1, y) <- Map.toList g']
        _ -> Nothing
      | (x0, g) <- Map.toList f
    ]

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
