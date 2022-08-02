{-# LANGUAGE OverloadedStrings #-}


module OSL.ValidateContext (validateContext) where


import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.Text (pack)

import OSL.Term (termAnnotation)
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
        Just _ -> Left (ErrorMessage ann "expected a type but got a term")
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
    Just _ -> Left (ErrorMessage ann "expected a type but got a term")
    Nothing -> Left (ErrorMessage ann "reference to undefined name")


getNamedTermType :: ValidContext ann -> ann -> Name -> Either (ErrorMessage ann) (Type ann)
getNamedTermType c ann name =
  case getDeclaration c name of
    Just (FreeVariable t) -> return t
    Just (Defined t _) -> return t
    Just _ -> Left (ErrorMessage ann "expected a term but got a type")
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
        Just (Defined t' _) -> checkTypeEquality c ann t t'
        Just (FreeVariable t') -> checkTypeEquality c ann t t'
        Just (Data _) -> Left (ErrorMessage ann "expected a term but got a type")
        Nothing -> Left (ErrorMessage ann "reference to undefined name")
    AddN ann -> checkTypeEquality c ann t (F ann (N ann) (F ann (N ann) (N ann)))
    MulN ann -> checkTypeEquality c ann t (F ann (N ann) (F ann (N ann) (N ann)))
    ConstN ann n -> do
      checkTypeEquality c ann t (N ann)
      if n >= 0
        then return ()
        else Left (ErrorMessage ann "expected a natural number but got a negative integer")
    AddZ ann -> checkTypeEquality c ann t (F ann (Z ann) (F ann (Z ann) (Z ann)))
    MulZ ann -> checkTypeEquality c ann t (F ann (Z ann) (F ann (Z ann) (Z ann)))
    ConstZ ann _ -> checkTypeEquality c ann t (Z ann)
    Cast ann ->
      case t of
        F _ a b -> checkTypeIsNumeric c a >> checkTypeIsNumeric c b
        a -> Left . ErrorMessage ann $ "expected a " <> pack (show a) <> " but got cast"
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
        F ann1 (Product _ a _) a' -> checkTypeEquality c ann1 a a'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got pi1"
    Pi2 ann0 ->
      case t of
        F ann1 (Product _ _ b) b' -> checkTypeEquality c ann1 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got pi2"
    Iota1 ann0 ->
      case t of
        F ann1 a (Coproduct _ a' _) -> checkTypeEquality c ann1 a a'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got iota1"
    Iota2 ann0 ->
      case t of
        F ann1 b (Coproduct _ _ b') -> checkTypeEquality c ann1 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got iota1"
    FunctionProduct _ f g ->
      case t of
        F ann1 a (Product _ b d) -> do
          checkTerm c (F ann1 a b) f
          checkTerm c (F ann1 a d) g
        _ -> genericErrorMessage
    FunctionCoproduct _ f g ->
      case t of
        F ann1 (Coproduct _ a b) d -> do
          checkTerm c (F ann1 a d) f
          checkTerm c (F ann1 b d) g
        _ -> genericErrorMessage
    Lambda ann varName varType def ->
      case t of
        F _ a _ -> do
          checkTypeEquality c ann a varType
          c' <- addToContext c (varName, FreeVariable varType)
          checkTerm c' t def
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
              <> " but got a lambda"
    Apply _ (Cast _) y -> do
      checkTypeIsNumeric c t
      a <- inferType c y
      checkTypeIsNumeric c a
  where
    genericErrorMessage = Left . ErrorMessage (termAnnotation x)
      $ "expected a " <> pack (show t) <> " but got " <> pack (show x)


inferType :: Show ann => ValidContext ann -> Term ann -> Either (ErrorMessage ann) (Type ann)
inferType c t =
  case t of
    NamedTerm ann name -> getNamedTermType c ann name
    ConstN ann _ -> return (N ann)
    ConstZ ann _ -> return (Z ann)
    ConstFin ann _ -> Left (ErrorMessage ann "cannot infer cardinality of type of finite constant")
    NamedTerm ann name -> getNamedTermType c ann name
    AddN ann -> return (F ann (N ann) (F ann (N ann) (N ann)))
    MulN ann -> return (F ann (N ann) (F ann (N ann) (N ann)))
    Cast ann -> Left (ErrorMessage ann "cannot infer the type of cast from context")
    Maybe' ann f -> do
      a <- inferType c f
      case a of
        F _ b d -> return (F ann d (F ann (Maybe ann b) d))
        _ -> Left . ErrorMessage ann $ "expected a function as the first argument to maybe but got a " <> pack (show a)
    Apply ann0 (Apply ann1 (Pair _) x) y -> do
      a <- inferType c x
      b <- inferType c y
      return (Product ann0 a b)
    Apply ann (Pi1 _) x -> do
      a <- inferType c x
      case a of
        Product _ b _ -> return b
        _ -> Left (ErrorMessage ann "pi1 applied to a non-tuple")
    Apply ann (Pi2 _) x -> do
      a <- inferType c x
      case a of
        Product _ _ b -> return b
        _ -> Left (ErrorMessage ann "pi2 applied to a non-tuple")
    Apply ann (Just' _) x -> Maybe ann <$> inferType c x
    Apply ann (Exists _) x -> do
      a <- inferType c x
      case a of
        Maybe _ b -> return b
        _ -> Left (ErrorMessage ann "exists applied to a non-Maybe")
    Apply ann (Nth _) xs -> do
      a <- inferType c xs
      case a of
        List _ b -> return (F ann (N ann) b)
        _ -> Left (ErrorMessage ann "nth applied to a non-List")
    Apply ann (ListPi1 _) xs -> do
      a <- inferType c xs
      case a of
        List _ (Product _ a _) -> return (List ann a)
        _ -> Left (ErrorMessage ann "List(pi1) applied to a non-List or a List of non-tuples")
    Apply ann (ListPi2 _) xs -> do
      a <- inferType c xs
      case a of
        List _ (Product _ _ b) -> return (List ann b)
        _ -> Left (ErrorMessage ann "List(pi2) applied to a non-List or a List of non-tuples")
    Apply ann (ListLength _) xs -> do
      a <- inferType c xs
      case a of
        List _ (List _ b) -> return (List ann (N ann))
        _ -> Left (ErrorMessage ann "List(length) applied to a non-List-of-Lists")
    Apply ann (ListMaybePi1 _) xs -> do
      a <- inferType c xs
      case a of
        List _ (Maybe _ (Product _ b _)) -> return (List ann (Maybe ann b))
        _ -> Left (ErrorMessage ann "List(Maybe(pi1)) applied to a non-List-of-Maybe-tuples")
    Apply ann (ListMaybePi2 _) xs -> do
      a <- inferType c xs
      case a of
        List _ (Maybe _ (Product _ _ b)) -> return (List ann (Maybe ann b))
        _ -> Left (ErrorMessage ann "List(Maybe(pi2)) applied to a non-List-of-Maybe-tuples")
    Apply ann (ListMaybeLength _) xs -> do
      a <- inferType c xs
      case a of
        List _ (Maybe _ (List _ b)) -> return (List ann (Maybe ann (N ann)))
        _ -> Left (ErrorMessage ann "List(Maybe(length)) applied to a non-List-of-Maybe-Lists")
    Apply ann (Sum _) xs -> todo
    Apply ann (Apply _ (Lookup _) k) xs -> todo
    Apply ann (Keys _) xs -> todo
    Apply ann (MapPi1 _) xs -> todo
    Apply ann (MapPi2 _) xs -> todo
    Apply ann (SumMapLength _) xs -> todo
    Apply ann (SumListLookup _ k) xs -> todo
    -- generic application inference for those cases not covered above
    Apply ann f x -> do
      a <- inferType c f
      case a of
        F _ b d -> do
          checkTerm c b x
          return d
    Lambda ann varName domain def -> do
      checkType c domain
      c' <- addToContext c (varName, FreeVariable domain)
      codomain <- inferType c def
      return (F ann domain codomain)
    Let ann varName varType def body -> todo


todo :: a
todo = todo


checkTypeIsNumeric :: Show ann => ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkTypeIsNumeric c t =
  case t of
    N _ -> return ()
    Z _ -> return ()
    Fin _ n -> return ()
    NamedType ann name -> getNamedType c ann name >>= checkTypeIsNumeric c
    t -> Left . ErrorMessage (typeAnnotation t) $ "expected a numeric type but got " <> pack (show t)
