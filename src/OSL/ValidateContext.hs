{-# LANGUAGE OverloadedStrings #-}


module OSL.ValidateContext (validateContext) where


import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.Text (pack)

import OSL.Type (typeAnnotation)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Name (..), Declaration (..), Type (..), Term (..), Context (..), ValidContext (..))
import OSL.ValidContext (getDeclaration)


validateContext :: Show ann => Context ann -> Either (ErrorMessage ann) (ValidContext ann)
validateContext = foldM addToContext (ValidContext mempty) . unContext


addToContext :: Show ann => ValidContext ann -> (Name, Declaration ann) -> Either (ErrorMessage ann) (ValidContext ann)
addToContext c@(ValidContext decls) (name, decl) = do
  let c' = ValidContext (Map.insert name decl decls)
  case decl of
    FreeVariable t -> checkType c t
    Data t -> checkType c t
    Defined t def -> do
      checkType c t
      checkTerm c t def
  return c'


checkType :: ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkType c t =
  case t of
    Prop _ -> return ()
    F _ a b -> checkType c a >> checkType c b
    N _ -> return ()
    Z _ -> return ()
    (Fin ann n) -> checkFinType ann n
    Product _ a b -> checkType c a >> checkType c b
    Coproduct _ a b -> checkType c a >> checkType c b
    NamedType ann name ->
      case getDeclaration c name of
        Just (Data _) -> return ()
        Just _ -> Left (ErrorMessage ann "expected a type but got a value")
        Nothing -> Left (ErrorMessage ann "reference to undefined name")
    Maybe _ a -> checkQuantifiableType c a
    List _ a -> checkQuantifiableType c a
    Map _ a b -> checkQuantifiableType c a >> checkFiniteDimType c b


checkFinType :: ann -> Integer -> Either (ErrorMessage ann) ()
checkFinType ann n =
  if n >= 0
  then return ()
  else Left (ErrorMessage ann "Fin type has a negative cardinality")


getNamedType :: ValidContext ann -> ann -> Name -> Either (ErrorMessage ann) (Type ann)
getNamedType c ann name =
  case getDeclaration c name of
    Just (Data t) -> return t
    Just _ -> Left (ErrorMessage ann "expected a type but got a value")
    Nothing -> Left (ErrorMessage ann "reference to undefined name")


checkQuantifiableType :: ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkQuantifiableType c t =
  case t of
    Prop ann -> Left (ErrorMessage ann "expected a quantifiable type but got Prop")
    F _ a b -> checkFiniteDimType c a >> checkQuantifiableType c b
    N _ -> return ()
    Z _ -> return ()
    Fin ann n -> checkFinType ann n
    Product _ a b -> checkQuantifiableType c a >> checkQuantifiableType c b
    Coproduct _ a b -> checkQuantifiableType c a >> checkQuantifiableType c b
    NamedType ann name -> getNamedType c ann name >>= checkQuantifiableType c
    Maybe _ a -> checkQuantifiableType c a
    List _ a -> checkQuantifiableType c a
    Map _ a b -> checkFiniteDimType c a >> checkQuantifiableType c b


checkFiniteDimType :: ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkFiniteDimType c t =
  case t of
    Prop ann -> Left (ErrorMessage ann "expected a finite-dimensional type but got Prop")
    F _ a b -> checkFiniteDimType c a >> checkFiniteDimType c b
    N _ -> return ()
    Z _ -> return ()
    Fin ann n -> checkFinType ann n
    Product _ a b -> checkFiniteDimType c a >> checkFiniteDimType c b
    Coproduct _ a b -> checkFiniteDimType c a >> checkFiniteDimType c b
    NamedType ann name -> getNamedType c ann name >>= checkFiniteDimType c
    Maybe _ a -> checkFiniteDimType c a
    List _ a -> checkFiniteDimType c a
    Map _ a b -> checkFiniteDimType c a >> checkFiniteDimType c b


checkTypeEquality :: Show ann => ValidContext ann -> ann -> Type ann -> Type ann -> Either (ErrorMessage ann) ()
checkTypeEquality _ _ (Prop _) (Prop _) = return ()
checkTypeEquality c ann (F _ a b) (F _ a' b') =
  checkTypeEquality c ann a a' >> checkTypeEquality c ann b b'
checkTypeEquality _ _ (N _) (N _) = return ()
checkTypeEquality _ _ (Z _) (Z _) = return ()
checkTypeEquality _ ann (Fin _ n) (Fin _ n') =
  if n == n'
  then return ()
  else Left (ErrorMessage ann "finite type cardinality mismatch")
checkTypeEquality c ann (Product _ a b) (Product _ a' b') =
  checkTypeEquality c ann a a' >> checkTypeEquality c ann b b'
checkTypeEquality c ann (Coproduct _ a b) (Coproduct _ a' b') =
  checkTypeEquality c ann a a' >> checkTypeEquality c ann b b'
checkTypeEquality _ ann (NamedType _ name) (NamedType _ name') =
  if name == name'
  then return ()
  else Left (ErrorMessage ann ("type mismatch: " <> unName name <> " and " <> unName name'))
checkTypeEquality c ann (Maybe _ a) (Maybe _ b) =
  checkTypeEquality c ann a b
checkTypeEquality c ann (List _ a) (List _ b) =
  checkTypeEquality c ann a b
checkTypeEquality c ann (Map _ a b) (Map _ a' b') =
  checkTypeEquality c ann a a' >> checkTypeEquality c ann b b'
checkTypeEquality _ ann t t' =
  Left . ErrorMessage ann $ "type mismatch: " <> pack (show t) <> " and " <> pack (show t')


checkTerm :: Show ann => ValidContext ann -> Type ann -> Term ann -> Either (ErrorMessage ann) ()
checkTerm c t x =
  case x of
    NamedTerm ann name ->
      case getDeclaration c name of
        Just (Defined t' def) -> checkTypeEquality c ann t t'
        Just (FreeVariable t') -> checkTypeEquality c ann t t'
        Just (Data _) -> Left (ErrorMessage ann "expected a value but got a type")
    AddN ann -> checkTypeEquality c ann t (F ann (N ann) (F ann (N ann) (N ann)))
    MulN ann -> checkTypeEquality c ann t (F ann (N ann) (F ann (N ann) (N ann)))
    ConstN ann n -> do
      checkTypeEquality c ann t (N ann)
      if n >= 0
        then return ()
        else Left (ErrorMessage ann "expected a natural number but got a negative integer")
    AddZ ann -> checkTypeEquality c ann t (F ann (Z ann) (F ann (Z ann) (Z ann)))
    MulZ ann -> checkTypeEquality c ann t (F ann (Z ann) (F ann (Z ann) (Z ann)))
    ConstZ ann n -> checkTypeEquality c ann t (Z ann)
    Cast ann ->
      case t of
        F _ a b -> checkTypeIsNumeric c a >> checkTypeIsNumeric c b
        t -> Left . ErrorMessage ann $ "expected a " <> pack (show t) <> " but got cast"
    ConstFin ann n ->
      case t of
        Fin _ m ->
          if n < 0
          then Left . ErrorMessage ann $ "expected an element of a finite type but got a negative number"
          else if n >= m
          then Left . ErrorMessage ann $ "expected an element of Fin(" <> pack (show m) <> ") but got " <> pack (show n)
          else return ()
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t) <> " but got a constant of a finite type"
    Pair ann0 ->
      case t of
        F ann1 a (F ann2 b (Product _ a' b')) -> do
          checkTypeEquality c ann1 a a'
          checkTypeEquality c ann2 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got the pairing function"
    Pi1 ann0 ->
      case t of
        F ann1 (Product _ a b) a' -> checkTypeEquality c ann1 a a'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got pi1"
    Pi2 ann0 ->
      case t of
        F ann1 (Product _ a b) b' -> checkTypeEquality c ann1 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got pi2"
    Iota1 ann0 ->
      case t of
        F ann1 a (Coproduct _ a' b) -> checkTypeEquality c ann1 a a'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got iota1"



checkTypeIsNumeric :: Show ann => ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkTypeIsNumeric c t =
  case t of
    N _ -> return ()
    Z _ -> return ()
    Fin _ n -> return ()
    NamedType ann name -> getNamedType c ann name >>= checkTypeIsNumeric c
    t -> Left . ErrorMessage (typeAnnotation t) $ "expected a numeric type but got " <> pack (show t)
