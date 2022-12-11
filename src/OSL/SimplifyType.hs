{-# LANGUAGE LambdaCase #-}

module OSL.SimplifyType
  ( simplifyType,
    simplifyValue,
    complexifyValue
  ) where

import Data.Maybe (fromMaybe)
import OSL.Types.OSL (Type (Prop, F, P, N, Z, Fp, Fin, Product, Coproduct, NamedType, Maybe, List, Map))
import OSL.Types.Value (Value)

-- This operation cannot fail. A result of Nothing
-- signifies that the type simplifies to the unit type
-- (i.e., no information).
simplifyType :: Type ann -> Maybe (Type ann)
simplifyType =
  \case
    Prop ann -> pure (Prop ann)
    F ann n a b -> do
      b' <- rec b
      case rec a of
        Just a' -> pure (F ann n a' b')
        Nothing -> pure b'
    P ann n a b ->
      P ann n <$> rec a <*> rec b
    N ann -> pure (N ann)
    Z ann -> pure (Z ann)
    Fp ann -> pure (Fp ann)
    Fin _ 1 -> Nothing
    Fin ann n -> pure (Fin ann n)
    Product ann a b ->
      case rec a of
        Nothing -> rec b
        Just a' ->
          case rec b of
            Nothing -> pure a'
            Just b' -> pure (Product ann a' b')
    Coproduct ann a b ->
      case rec a of
        Nothing -> rec b
        Just a' ->
          case rec b of
            Nothing -> pure a'
            Just b' -> pure (Coproduct ann a' b')
    NamedType ann name -> pure (NamedType ann name)
    Maybe ann a ->
      pure (Maybe ann (rec' ann a))
    List ann n a ->
      pure (List ann n (rec' ann a))
    Map ann n a b ->
      case rec a of
        Just a' -> pure (Map ann n a' (rec' ann b))
        Nothing -> pure b
  where
    rec = simplifyType

    rec' ann = fromMaybe (Fin ann 1) . rec

simplifyValue :: Type ann -> Value -> Value
simplifyValue = todo

complexifyValue :: Type ann -> Value -> Value
complexifyValue = todo

todo :: a
todo = todo
