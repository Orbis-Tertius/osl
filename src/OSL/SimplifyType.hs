{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.SimplifyType
  ( simplifyType,
    simplifyValue,
    complexifyValue,
    complexifyValueUnsafe
  ) where

import Control.Lens ((^.))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (pack)
import Die (die)
import OSL.Type (typeAnnotation, dropTypeAnnotations)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.OSL (Type (Prop, F, P, N, Z, Fp, Fin, Product, Coproduct, NamedType, Maybe, List, Map), ValidContext, ContextType (Global), Declaration (Data))
import OSL.Types.Value (Value (Bool, Fun, Fin', Nat, Int, Fp', Pair', Iota1', Iota2', Maybe'', List'', Map'', To', Maybe''))

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
      (P _ann _n a b, Fun f) ->
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
      (N _ann, Nat x) -> pure (Nat x)
      (Z _ann, Int x) -> pure (Int x)
      (Fp _ann, Fp' x) -> pure (Fp' x)
      (Fin _ann _, Fin' x) -> pure (Fin' x)
      (Product _ann a b, Pair' x y) ->
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
      (NamedType {}, x) -> pure x
      (Maybe _ann _a, Maybe'' Nothing) -> pure (Maybe'' Nothing)
      (Maybe _ann a, Maybe'' (Just x)) ->
        Maybe'' . Just <$> simplifyValue a x
      (List _ann _n a, List'' xs) ->
        List'' <$> mapM (simplifyValue a) xs
      (Map _ann _n a b, Map'' xs) ->
         case simplifyType b of
           Nothing -> pure (Fin' 0)
           Just _ ->
             Map'' . Map.fromList <$> sequence
               [ (,) <$> simplifyValue a x <*> simplifyValue b y
               | (x,y) <- Map.toList xs
               ]
      (t, _) -> Left . ErrorMessage (typeAnnotation t)
        $ "simplifyValue: type error"

complexifyValueUnsafe :: ValidContext 'Global ann -> Type () -> Value -> Value
complexifyValueUnsafe c t x =
  case complexifyValue c t x of
    Right y -> y
    Left err -> die (pack (show err))

complexifyValue :: ValidContext 'Global ann -> Type () -> Value -> Either (ErrorMessage ()) Value
complexifyValue c =
  curry $
    \case
      (Prop _, Bool x) -> pure (Bool x)
      (Prop _, Fin' 0) -> pure (Bool False)
      (F ann _n a b, x) ->
        case simplifyType a of
          Nothing -> do
            k <- rec a (Fin' 0)
            x' <- rec b x
            pure (Fun (Map.singleton k x'))
          Just _ ->
            case x of
              Fun f ->
                Fun . Map.fromList <$> sequence
                  [ (,) <$> rec a y <*> rec b z
                  | (y,z) <- Map.toList f
                  ]
              _ -> Left . ErrorMessage ann $
                "complexifyValue: type error"
      (P ann _n a b, x) ->
        case simplifyType a of
          Nothing -> pure (Fun (Map.fromList [(Fin' 0, Fin' 0)]))
          Just _ ->
            case x of
              Fun f ->
                Fun . Map.fromList <$> sequence
                  [ (,) <$> rec a y <*> rec b z
                  | (y,z) <- Map.toList f
                  ]
              _ -> Left . ErrorMessage ann $
                "complexifyValue: type error"
      (N _, Nat x) -> pure (Nat x) 
      (N _, Fin' 0) -> pure (Nat 0)
      (Z _, Int x) -> pure (Int x)
      (Fp _, Fp' x) -> pure (Fp' x)
      (Fp _, Fin' 0) -> pure (Fp' 0)
      (Fin {}, Fin' x) -> pure (Fin' x)
      (Product ann a b, z) ->
        case simplifyType a of
          Nothing ->
            case simplifyType b of
              Nothing ->
                case z of
                  Fin' 0 ->
                    Pair' <$> rec a (Fin' 0) <*> rec b (Fin' 0)
                  _ -> Left . ErrorMessage ann $
                    "complexifyValue: type error"
              Just _ ->
                Pair' <$> rec a (Fin' 0) <*> rec b z
          Just _ ->
            case simplifyType b of
              Nothing ->
                Pair' <$> rec a z <*> rec b (Fin' 0)
              Just _ ->
                case z of
                  Pair' x y -> Pair' <$> rec a x <*> rec b y
                  _ -> Left . ErrorMessage ann $
                    "complexifyValue: type error"
      (Coproduct _ann a _b, Iota1' x) ->
        Iota1' <$> rec a x
      (Coproduct _ann _a b, Iota2' x) ->
        Iota2' <$> rec b x
      (Coproduct _ann a _b, Fin' 0) ->
        Iota1' <$> rec a (Fin' 0)
      (NamedType ann name, To' name' x) ->
        case Map.lookup name (c ^. #unValidContext) of
          Just (Data a) ->
            if name == name'
            then To' name <$> rec (dropTypeAnnotations a) x
            else Left . ErrorMessage ann $ "complexifyValue: type error"
          _ -> Left . ErrorMessage ann $
            "complexifyValue: expected the name of a type"
      (NamedType ann name, Fin' 0) ->
        case Map.lookup name (c ^. #unValidContext) of
          Just (Data a) ->
            To' name <$> rec (dropTypeAnnotations a) (Fin' 0)
          _ -> Left . ErrorMessage ann $
            "complexifyValue: expected the name of a type"
      (Maybe {}, Maybe'' Nothing) ->
        pure (Maybe'' Nothing)
      (Maybe _ann a, Maybe'' (Just x)) ->
        Maybe'' . Just <$> rec a x
      (Maybe _ann _a, Fin' 0) -> pure (Maybe'' Nothing)
      (List _ann _n a, List'' xs) ->
        List'' <$> mapM (rec a) xs
      (List _ann _n _a, Fin' 0) ->
        pure (List'' [])
      (Map _ann _n a b, Map'' xs) ->
        Map'' . Map.fromList <$> sequence
          [ (,) <$> rec a x <*> rec b y
          | (x,y) <- Map.toList xs
          ]
      (Map {}, Fin' 0) -> pure (Map'' mempty)
      (t, _) -> Left . ErrorMessage (typeAnnotation t)
        $ "complexifyValue: type error"
  where
    rec = complexifyValue c
