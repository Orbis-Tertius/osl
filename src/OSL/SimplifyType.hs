{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.SimplifyType
  ( simplifyType,
    simplifyValue,
    complexifyValue
  ) where

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.OSL (Type (Prop, F, P, N, Z, Fp, Fin, Product, Coproduct, NamedType, Maybe, List, Map))
import OSL.Types.Value (Value (Bool, Fun, Fin', Nat, Int, Fp', Pair', Iota1', Iota2'))

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

simplifyValue :: Type ann -> Value -> Either (ErrorMessage ann) Value
simplifyValue =
  curry $
    \case
      (Prop _, Bool v) -> pure (Bool v)
      (F ann _n a b, Fun f) ->
        case simplifyType b of
          Nothing -> pure (Fin' 0)
          Just _ ->
            case simplifyType a of
              Nothing ->
                case Map.lookup (Fin' 0) f of
                  Just v -> simplifyValue b v
                  Nothing -> Left . ErrorMessage ann $
                    "function not defined on value fin(0)"
              Just _ ->
                Fun . Map.fromList <$> sequence
                  [ (,) <$> simplifyValue a x <*> simplifyValue b y
                  | (x,y) <- Map.toList f
                  ]
      (P ann _n a b, Fun f) ->
        case simplifyType b of
          Nothing -> pure (Fin' 0)
          Just _ ->
            case simplifyType a of
              Nothing -> pure (Fin' 0)
              Just _ ->
                Fun . Map.fromList <$> sequence
                  [ (,) <$> simplifyValue a x <*> simplifyValue b y
                  | (x,y) <- Map.toList f
                  ]
      (N ann, Nat x) -> pure (Nat x)
      (Z ann, Int x) -> pure (Int x)
      (Fp ann, Fp' x) -> pure (Fp' x)
      (Fin ann _, Fin' x) -> pure (Fin' x)
      (Product ann a b, Pair' x y) ->
        case simplifyType a of
          Nothing ->
            case simplifyType b of
              Nothing -> pure (Fin' 0)
              Just _ -> simplifyValue b y
          Just _ ->
            case simplifyType b of
              Nothing -> simplifyValue a x
              Just _ -> Pair' <$> simplifyValue a x <*> simplifyValue b y
      (t@(Coproduct ann a b), x) ->
        case simplifyType t of
          Nothing -> pure (Fin' 0)
          Just _ ->
            case x of
              Iota1' y -> Iota1' <$> simplifyValue a y
              Iota2' y -> Iota2' <$> simplifyValue b y
              _ -> Left . ErrorMessage ann $ "simplifyValue: type error"

complexifyValue :: Type ann -> Value -> Value
complexifyValue = todo

todo :: a
todo = todo
