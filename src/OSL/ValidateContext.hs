{-# LANGUAGE OverloadedStrings #-}


module OSL.ValidateContext
  ( validateContext
  , inferType
  ) where


import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.Text (pack)

import OSL.Term (termAnnotation, boundAnnotation)
import OSL.Type (typeAnnotation)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Name (..), Declaration (..), Type (..), Term (..), Context (..), ValidContext (..), Bound (..), LeftBound (..), RightBound (..), DomainBound (..), CodomainBound (..), ValuesBound (..), KeysBound (..), Cardinality (..))
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
    F ann n a b -> checkMaybeCardinality ann n >> checkType c a >> checkType c b
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
    List ann n a -> checkCardinality ann n >> checkQuantifiableType c a
    Map ann n a b -> checkCardinality ann n
      >> checkQuantifiableType c a
      >> checkFiniteDimType c b


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
    F ann n a b -> checkFiniteDimType c a
      >> checkMaybeCardinality ann n
      >> checkQuantifiableType c b
    N _ -> return ()
    Z _ -> return ()
    Fin ann n -> checkFinType ann n
    Product _ a b -> checkQuantifiableType c a >> checkQuantifiableType c b
    Coproduct _ a b -> checkQuantifiableType c a >> checkQuantifiableType c b
    NamedType ann name -> getNamedType c ann name >>= checkQuantifiableType c
    Maybe _ a -> checkQuantifiableType c a
    List ann n a -> checkCardinality ann n >> checkQuantifiableType c a
    Map ann n a b -> checkCardinality ann n
      >> checkFiniteDimType c a
      >> checkQuantifiableType c b


checkFiniteDimType :: ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkFiniteDimType c t =
  case t of
    Prop ann -> Left (ErrorMessage ann "expected a finite-dimensional type but got Prop")
    F ann n a b -> checkMaybeCardinality ann n
      >> checkFiniteDimType c a
      >> checkFiniteDimType c b
    N _ -> return ()
    Z _ -> return ()
    Fin ann n -> checkFinType ann n
    Product _ a b -> checkFiniteDimType c a >> checkFiniteDimType c b
    Coproduct _ a b -> checkFiniteDimType c a >> checkFiniteDimType c b
    NamedType ann name -> getNamedType c ann name >>= checkFiniteDimType c
    Maybe _ a -> checkFiniteDimType c a
    List ann n a -> checkCardinality ann n >> checkFiniteDimType c a
    Map ann n a b -> checkCardinality ann n
      >> checkFiniteDimType c a
      >> checkFiniteDimType c b


checkTypeInclusion :: Show ann => ValidContext ann -> ann -> Type ann -> Type ann -> Either (ErrorMessage ann) ()
checkTypeInclusion _ _ (Prop _) (Prop _) = return ()
checkTypeInclusion c ann (F _ _ a b) (F _ Nothing a' b') =
  checkTypeInclusion c ann a' a >> checkTypeInclusion c ann b b'
checkTypeInclusion _ ann (F _ Nothing _ _) (F _ (Just _) _ _) =
  Left (ErrorMessage ann "function type cardinality mismatch")
checkTypeInclusion c ann (F _ (Just n) a b) (F _ (Just n') a' b') =
  if n <= n'
  then checkTypeInclusion c ann a' a >> checkTypeInclusion c ann b b'
  else Left (ErrorMessage ann "function type cardinality mismatch")
checkTypeInclusion _ _ (N _) (N _) = return ()
checkTypeInclusion _ _ (Z _) (Z _) = return ()
checkTypeInclusion _ ann (Fin _ n) (Fin _ n') =
  if n <= n'
  then return ()
  else Left (ErrorMessage ann "finite type cardinality mismatch")
checkTypeInclusion c ann (Product _ a b) (Product _ a' b') =
  checkTypeInclusion c ann a a' >> checkTypeInclusion c ann b b'
checkTypeInclusion c ann (Coproduct _ a b) (Coproduct _ a' b') =
  checkTypeInclusion c ann a a' >> checkTypeInclusion c ann b b'
checkTypeInclusion _ ann (NamedType _ name) (NamedType _ name') =
  if name == name'
  then return ()
  else Left (ErrorMessage ann ("type mismatch: " <> pack (show name) <> " and " <> pack (show name')))
checkTypeInclusion c ann (Maybe _ a) (Maybe _ b) =
  checkTypeInclusion c ann a b
checkTypeInclusion c ann (List _ n a) (List _ m b) =
  if n <= m
  then checkTypeInclusion c ann a b
  else Left (ErrorMessage ann "list type cardinality mismatch")
checkTypeInclusion c ann (Map _ n a b) (Map _ n' a' b') =
  if n <= n'
  then checkTypeInclusion c ann a a' >> checkTypeInclusion c ann b b'
  else Left (ErrorMessage ann "map type cardinality mismatch")
checkTypeInclusion _ ann t t' =
  Left . ErrorMessage ann $ "type mismatch: " <> pack (show t) <> " and " <> pack (show t')


checkTerm :: Show ann => ValidContext ann -> Type ann -> Term ann -> Either (ErrorMessage ann) ()
checkTerm c t x =
  case x of
    NamedTerm ann name ->
      case getDeclaration c name of
        Just (Defined t' _) -> checkTypeInclusion c ann t t'
        Just (FreeVariable t') -> checkTypeInclusion c ann t t'
        Just (Data _) -> Left (ErrorMessage ann "expected a term but got a type")
        Nothing -> Left (ErrorMessage ann "reference to undefined name")
    AddN ann -> checkTypeInclusion c ann t
       (F ann Nothing (N ann) (F ann Nothing (N ann) (N ann)))
    MulN ann -> checkTypeInclusion c ann t
       (F ann Nothing (N ann) (F ann Nothing (N ann) (N ann)))
    ConstN ann n -> do
      checkTypeInclusion c ann t (N ann)
      if n >= 0
        then return ()
        else Left (ErrorMessage ann "expected a natural number but got a negative integer")
    AddZ ann -> checkTypeInclusion c ann t
      (F ann Nothing (Z ann) (F ann Nothing (Z ann) (Z ann)))
    MulZ ann -> checkTypeInclusion c ann t
      (F ann Nothing (Z ann) (F ann Nothing (Z ann) (Z ann)))
    ConstZ ann _ -> checkTypeInclusion c ann t (Z ann)
    Cast ann ->
      case t of
        F _ _ a b -> checkTypeIsNumeric c a >> checkTypeIsNumeric c b
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
        F ann1 _ a (F ann2 _ b (Product _ a' b')) -> do
          checkTypeInclusion c ann1 a a'
          checkTypeInclusion c ann2 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got the pairing function"
    Pi1 ann0 ->
      case t of
        F ann1 _ (Product _ a _) a' -> checkTypeInclusion c ann1 a a'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got pi1"
    Pi2 ann0 ->
      case t of
        F ann1 _ (Product _ _ b) b' -> checkTypeInclusion c ann1 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got pi2"
    Iota1 ann0 ->
      case t of
        F ann1 _ a (Coproduct _ a' _) -> checkTypeInclusion c ann1 a a'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got iota1"
    Iota2 ann0 ->
      case t of
        F ann1 _ b (Coproduct _ _ b') -> checkTypeInclusion c ann1 b b'
        _ -> Left . ErrorMessage ann0 $ "expected a " <> pack (show t) <> " but got iota1"
    FunctionProduct _ f g ->
      case t of
        F ann1 n a (Product _ b d) -> do
          checkTerm c (F ann1 n a b) f
          checkTerm c (F ann1 n a d) g
        _ -> genericErrorMessage
    FunctionCoproduct _ f g ->
      case t of
        F ann1 n (Coproduct _ a b) d -> do
          checkTerm c (F ann1 n a d) f
          checkTerm c (F ann1 n b d) g
        _ -> genericErrorMessage
    Lambda ann varName varType def ->
      case t of
        F _ _ a b -> do
          checkTypeInclusion c ann a varType
          c' <- addToContext c (varName, FreeVariable varType)
          checkTerm c' b def
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
              <> " but got a lambda"
    Apply _ (Cast _) y -> do
      checkTypeIsNumeric c t
      a <- inferType c y
      checkTypeIsNumeric c a
    Apply ann f y -> do
      case inferType c f of
        Left _ -> do
          a <- inferType c y
          checkTerm c (F ann Nothing a t) f
        Right (F _ _ a b) -> do
          checkTerm c a y
          checkTypeInclusion c ann t b
        Right _ -> Left (ErrorMessage ann "function application head is not a function")
    To ann name -> do
      a <- getNamedType c ann name
      checkTypeInclusion c ann t (F ann Nothing a (NamedType ann name))
    From ann name -> do
      a <- getNamedType c ann name
      checkTypeInclusion c ann t (F ann Nothing (NamedType ann name) a)
    Let _ varName varType varDef body -> do
      checkType c varType
      c' <- addToContext c (varName, Defined varType varDef)
      checkTerm c' t body
    Just' ann ->
      case t of
        F _ _ a (Maybe _ a') -> checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    Nothing' _ ->
      case t of
        Maybe _ _ -> return ()
        _ -> genericErrorMessage
    Maybe' ann f ->
      case t of
        F _ n b (F _ _ (Maybe _ a) b') -> do
          checkTypeInclusion c ann b b'
          checkTerm c (F ann n a b) f
        _ -> genericErrorMessage
    Exists ann ->
      case t of
        F _ _ (Maybe _ a) a' -> checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    Length _ ->
      case t of
        F _ _ (List _ _ _) (N _) -> return ()
        _ -> genericErrorMessage
    Nth ann ->
      case t of
        F _ _ (List _ _ a) (F _ _ (N _) a') -> checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    ListPi1 ann ->
      case t of
        F _ _ (List _ _ (Product _ a _)) (List _ _ a') ->
          checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    ListPi2 ann ->
      case t of
        F _ _ (List _ _ (Product _ _ b)) (List _ _ b') ->
          checkTypeInclusion c ann b b'
        _ -> genericErrorMessage
    ListTo ann name -> do
      a <- getNamedType c ann name
      case t of
        F _ _ (List _ _ a') (List _ _ (NamedType _ name')) -> do
          checkTypeInclusion c ann a a'
          if name == name'
            then return ()
            else genericErrorMessage
        _ -> genericErrorMessage
    ListFrom ann name -> do
      a <- getNamedType c ann name
      case t of
        F _ _ (List _ _ (NamedType _ name')) (List _ _ a') -> do
          checkTypeInclusion c ann a a'
          if name == name'
            then return ()
            else genericErrorMessage
        _ -> genericErrorMessage
    ListMaybeTo ann name -> do
      a <- getNamedType c ann name
      case t of
        F _ _ (List _ _ (Maybe _ a')) (List _ _ (Maybe _ (NamedType _ name'))) -> do
          checkTypeInclusion c ann a a'
          if name == name'
            then return ()
            else genericErrorMessage
        _ -> genericErrorMessage
    ListMaybeFrom ann name -> do
      a <- getNamedType c ann name
      case t of
        F _ _ (List _ _ (Maybe _ (NamedType _ name'))) (List _ _ (Maybe _ a')) -> do
          checkTypeInclusion c ann a a'
          if name == name'
            then return ()
            else genericErrorMessage
        _ -> genericErrorMessage
    ListLength _ ->
      case t of
        F _ _ (List _ _ (List _ _ _)) (List _ _ (N _)) -> return ()
        _ -> genericErrorMessage
    ListMaybePi1 ann ->
      case t of
        F _ _ (List _ _ (Maybe _ (Product _ a _))) (List _ _ (Maybe _ a')) ->
          checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    ListMaybePi2 ann ->
      case t of
        F _ _ (List _ _ (Maybe _ (Product _ _ b))) (List _ _ (Maybe _ b')) ->
          checkTypeInclusion c ann b b'
        _ -> genericErrorMessage
    ListMaybeLength _ ->
      case t of
        F _ _ (List _ _ (Maybe _ (List _ _ _))) (List _ _ (Maybe _ (N _))) -> return ()
        _ -> genericErrorMessage
    Sum ann ->
      case t of
        F _ _ (List _ _ (Maybe _ a)) a' -> do
          checkTypeInclusion c ann a a'
          checkTypeIsNumeric c a
        F _ _ (List _ _ (List _ _ (Maybe _ a))) a' -> do
          checkTypeInclusion c ann a a'
          checkTypeIsNumeric c a
        F _ _ (List _ _ (List _ _ a)) a' -> do
          checkTypeInclusion c ann a a'
          checkTypeIsNumeric c a
        F _ _ (List _ _ a) a' -> do
         checkTypeInclusion c ann a a'
         checkTypeIsNumeric c a
        F _ _ (Map _ _ _ b) b' -> do
          checkTypeInclusion c ann b b'
          checkTypeIsNumeric c b
        _ -> genericErrorMessage
    Lookup ann ->
      case t of
        F _ _ a (F _ _ (Map _ _ a' b) (Maybe _ b')) -> do
          checkTypeInclusion c ann a a'
          checkTypeInclusion c ann b b'
        _ -> genericErrorMessage
    Keys ann ->
      case t of
        F _ _ (Map _ _ a _) (List _ _ a') ->
          checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    MapPi1 ann ->
      case t of
        F _ _ (Map _ _ a (Product _ b _)) (Map _ _ a' b') -> do
          checkTypeInclusion c ann a a'
          checkTypeInclusion c ann b b'
        _ -> genericErrorMessage
    MapPi2 ann ->
      case t of
        F _ _ (Map _ _ a (Product _ _ d)) (Map _ _ a' d') -> do
          checkTypeInclusion c ann a a'
          checkTypeInclusion c ann d d'
        _ -> genericErrorMessage
    MapTo ann name -> do
      a <- getNamedType c ann name
      case t of
        F _ _ (Map _ _ a' b) (Map _ _ (NamedType _ name') b') -> do
          checkTypeInclusion c ann a a'
          checkTypeInclusion c ann b b'
          if name' == name
            then return ()
            else genericErrorMessage
        _ -> genericErrorMessage
    MapFrom ann name -> do
      a <- getNamedType c ann name
      case t of
        F _ _ (Map _ _ (NamedType _ name') b) (Map _ _ a' b') -> do
          checkTypeInclusion c ann a a'
          checkTypeInclusion c ann b b'
          if name' == name
            then return ()
            else genericErrorMessage
        _ -> genericErrorMessage
    SumMapLength ann ->
      case t of
        F _ _ (Map _ _ a (List _ _ _)) (Map _ _ a' (N _)) ->
          checkTypeInclusion c ann a a'
        _ -> genericErrorMessage
    SumListLookup _ann0 k ->
      case t of
        F _ _ (List _ _ (Map ann1 _ a b)) b' -> do
          checkTypeInclusion c ann1 b b'
          checkTypeIsNumeric c b
          checkTerm c a k
        _ -> genericErrorMessage
    Equal _ y z -> do
      case t of
        Prop _ -> do
          a <- case inferType c y of
            Left _ -> do
              a <- inferType c z
              checkTerm c a y
              return a
            Right a -> do
              checkTerm c a z
              return a
          checkFiniteDimType c a
        _ -> genericErrorMessage
    LessOrEqual _ y z -> do
      case t of
        Prop _ -> do
          a <- case inferType c y of
            Left _ -> do
              a <- inferType c z
              checkTerm c a y
              return a
            Right a -> do
              checkTerm c a z
              return a
          checkTypeIsNumeric c a
        _ -> genericErrorMessage
    And ann p q -> do
      case t of
        Prop _ -> do
          checkTerm c (Prop ann) p
          checkTerm c (Prop ann) q
        _ -> genericErrorMessage
    Or ann p q -> do
      case t of
        Prop _ -> do
          checkTerm c (Prop ann) p
          checkTerm c (Prop ann) q
        _ -> genericErrorMessage
    Not ann p -> do
      case t of
        Prop _ -> checkTerm c (Prop ann) p
        _ -> genericErrorMessage
    Implies ann p q -> do
      case t of
        Prop _ -> do
          checkTerm c (Prop ann) p
          checkTerm c (Prop ann) q
        _ -> genericErrorMessage
    ForAll ann varName varType varBound p -> do
      checkType c varType
      maybe (pure ()) (checkBound c varType) varBound
      c' <- addToContext c (varName, FreeVariable varType)
      checkTerm c' (Prop ann) p
    ForSome ann varName varType varBound p -> do
      checkType c varType
      maybe (pure ()) (checkBound c varType) varBound
      c' <- addToContext c (varName, FreeVariable varType)
      checkTerm c' (Prop ann) p
  where
    genericErrorMessage = Left . ErrorMessage (termAnnotation x)
      $ "expected a " <> pack (show t) <> " but got " <> pack (show x)


checkBound
  :: Show ann
  => ValidContext ann
  -> Type ann
  -> Bound ann
  -> Either (ErrorMessage ann) ()
checkBound c t bound =
  case t of
    Prop ann -> Left (ErrorMessage ann "cannot quantify over Prop")
    F _ _ a b ->
      case bound of
        FunctionBound _ (DomainBound aBound) (CodomainBound bBound) -> do
          checkBound c a aBound
          checkBound c b bBound
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected a function bound")
    N ann' ->
      case bound of
        ScalarBound _ boundTerm -> checkTerm c (N ann') boundTerm
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected a natural number bound")
    Z ann' ->
      case bound of
        ScalarBound _ boundTerm -> checkTerm c (Z ann') boundTerm
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected an integer bound")
    Fin ann' n ->
      case bound of
        ScalarBound _ boundTerm -> checkTerm c (Fin ann' n) boundTerm
        _ -> Left . ErrorMessage (boundAnnotation bound)
              $ "expected a Fin(" <> pack (show n) <> ") bound"
    Product _ a b ->
      case bound of
        ProductBound _ (LeftBound aBound) (RightBound bBound) -> do
          checkBound c a aBound
          checkBound c b bBound
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected a product bound")
    Coproduct _ a b ->
      case bound of
        CoproductBound _ (LeftBound aBound) (RightBound bBound) -> do
          checkBound c a aBound
          checkBound c b bBound
        _ -> Left (ErrorMessage (boundAnnotation bound)
                    "expected a coproduct bound")
    NamedType ann' name ->
      case getDeclaration c name of
        Just (Data a) ->
          case bound of
            ToBound ann name' bound' ->
              if name == name'
              then checkBound c a bound'
              else Left (ErrorMessage ann "mismatching named type and to bound")
            _ -> Left (ErrorMessage (boundAnnotation bound)
                        "expected a to bound")
        _ -> Left (ErrorMessage ann' "expected the name of a type")
    Maybe _ a ->
      case bound of
        MaybeBound _ (ValuesBound bound') -> checkBound c a bound'
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected a maybe bound")
    List _ _ a ->
      case bound of
        ListBound _ (ValuesBound vBound) -> do
          checkBound c a vBound
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected a list bound")
    Map _ _ a b ->
      case bound of
        MapBound _ (KeysBound aBound)
                   (ValuesBound bBound) -> do
          checkBound c a aBound
          checkBound c b bBound
        _ -> Left (ErrorMessage (boundAnnotation bound)
                     "expected a map bound")


inferType
  :: Show ann
  => ValidContext ann
  -> Term ann
  -> Either (ErrorMessage ann) (Type ann)
inferType c t =
  case t of
    NamedTerm ann name -> getNamedTermType c ann name
    ConstN ann _ -> return (N ann)
    ConstZ ann _ -> return (Z ann)
    ConstFin ann _ -> Left (ErrorMessage ann "cannot infer cardinality of type of finite constant")
    AddN ann -> pure (F ann Nothing (N ann) (F ann Nothing (N ann) (N ann)))
    MulN ann -> pure (F ann Nothing (N ann) (F ann Nothing (N ann) (N ann)))
    AddZ ann -> pure (F ann Nothing (Z ann) (F ann Nothing (Z ann) (Z ann)))
    MulZ ann -> pure (F ann Nothing (Z ann) (F ann Nothing (Z ann) (Z ann)))
    Cast ann -> Left (ErrorMessage ann "cannot infer the type of cast from context")
    To ann name -> do
      a <- getNamedType c ann name
      return (F ann Nothing a (NamedType ann name))
    From ann name -> do
      a <- getNamedType c ann name
      return (F ann Nothing (NamedType ann name) a)
    FunctionProduct ann f g -> do
      a <- inferType c f
      b <- inferType c g
      case (a, b) of
        (F _ n d e, F _ n' d' e') -> do
          checkTypeInclusion c ann d d'
          return (F ann (min <$> n <*> n') d (Product ann e e'))
        _ -> Left (ErrorMessage ann "ill-typed function product; one of the arguments is not a function")
    FunctionCoproduct ann f g -> do
      a <- inferType c f
      b <- inferType c g
      case (a, b) of
        (F _ n d e, F _ m d' e') -> do
          checkTypeInclusion c ann e e'
          return (F ann (min <$> n <*> m) (Coproduct ann d d') e)
        _ -> Left (ErrorMessage ann "ill-typed function coproduct; one of the arguments is not a function")
    Maybe' ann f -> do
      a <- inferType c f
      case a of
        F _ n b d -> return (F ann n d (F ann n (Maybe ann b) d))
        _ -> Left . ErrorMessage ann $ "expected a function as the first argument to maybe but got a " <> pack (show a)
    Apply ann (Apply _ (Pair _) x) y -> do
      a <- inferType c x
      b <- inferType c y
      return (Product ann a b)
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
        List _ n b -> return (F ann (Just n) (N ann) b)
        _ -> Left (ErrorMessage ann "nth applied to a non-List")
    Apply ann (Length _) xs -> do
      a <- inferType c xs
      case a of
        List _ _ _ -> pure (N ann)
        _ -> Left (ErrorMessage ann "length applied to a non-List")
    Apply ann (ListPi1 _) xs -> do
      a <- inferType c xs
      case a of
        List _ n (Product _ b _) -> return (List ann n b)
        _ -> Left (ErrorMessage ann "List(pi1) applied to a non-List or a List of non-tuples")
    Apply ann (ListPi2 _) xs -> do
      a <- inferType c xs
      case a of
        List _ n (Product _ _ b) -> return (List ann n b)
        _ -> Left (ErrorMessage ann "List(pi2) applied to a non-List or a List of non-tuples")
    Apply ann (ListLength _) xs -> do
      a <- inferType c xs
      case a of
        List _ n (List _ _ _) -> return (List ann n (N ann))
        _ -> Left (ErrorMessage ann "List(length) applied to a non-List-of-Lists")
    Apply ann (ListMaybePi1 _) xs -> do
      a <- inferType c xs
      case a of
        List _ n (Maybe _ (Product _ b _)) -> return (List ann n (Maybe ann b))
        _ -> Left (ErrorMessage ann "List(Maybe(pi1)) applied to a non-List-of-Maybe-tuples")
    Apply ann (ListMaybePi2 _) xs -> do
      a <- inferType c xs
      case a of
        List _ n (Maybe _ (Product _ _ b)) -> return (List ann n (Maybe ann b))
        _ -> Left (ErrorMessage ann "List(Maybe(pi2)) applied to a non-List-of-Maybe-tuples")
    Apply ann (ListMaybeLength _) xs -> do
      a <- inferType c xs
      case a of
        List _ n (Maybe _ (List _ _ _)) ->
          return (List ann n (Maybe ann (N ann)))
        _ -> Left (ErrorMessage ann "List(Maybe(length)) applied to a non-List-of-Maybe-Lists")
    Apply ann (ListTo _ name) xs -> do
      a <- getNamedType c ann name
      xsT <- inferType c xs
      case xsT of
        List _ n a' -> do
          checkTypeInclusion c ann a a'
          pure (List ann n (NamedType ann name))
        _ -> Left (ErrorMessage ann "expected a list")
    Apply ann (ListMaybeTo _ name) xs -> do
      a <- getNamedType c ann name
      xsT <- inferType c xs
      case xsT of
        List _ n (Maybe _ a') -> do
          checkTypeInclusion c ann a a'
          pure (List ann n (Maybe ann (NamedType ann name)))
        _ -> Left (ErrorMessage ann "expected a list")
    Apply ann (ListMaybeFrom _ name) xs -> do
      a <- getNamedType c ann name
      xsT <- inferType c xs
      case xsT of
        List _ n (Maybe _ (NamedType _ name')) ->
          if name == name'
          then pure (List ann n (Maybe ann a))
          else Left (ErrorMessage ann "type name mismatch in inferring type of List(Maybe(from)) application")
        _ -> Left (ErrorMessage ann "expected a list of a named type")
    Apply ann (ListFrom _ name) xs -> do
      a <- getNamedType c ann name
      xsT <- inferType c xs
      case xsT of
        List _ n (NamedType _ name') ->
          if name == name'
          then pure (List ann n a)
          else Left (ErrorMessage ann "type name mismatch in inferring type of List(from) application")
        _ -> Left (ErrorMessage ann "expected a list of a named type")
    Apply ann (Sum _) xs -> do
      a <- inferType c xs
      case a of
        List _ _ (Maybe _ b) -> do
          checkTypeIsNumeric c b
          return b
        List _ _ (List _ _ (Maybe _ b)) -> do
          checkTypeIsNumeric c b
          return b
        List _ _ (List _ _ b) -> do
          checkTypeIsNumeric c b
          return b
        List _ _ b -> do
          checkTypeIsNumeric c b
          return b
        Map _ _ _ b -> do
          checkTypeIsNumeric c b
          return b
        _ -> Left (ErrorMessage ann "sum applied to a non-summable term")
    Apply ann (Apply _ (Lookup _) k) xs -> do
      a <- inferType c k
      b <- inferType c xs
      case b of
        Map _ _ a' d -> do
          checkTypeInclusion c ann a a'
          return (Maybe ann d)
        _ -> Left (ErrorMessage ann "lookup applied to a non-Map")
    Apply ann (Keys _) xs -> do
      a <- inferType c xs
      case a of
        Map _ n b _ -> return (List ann n b)
        _ -> Left (ErrorMessage ann "keys applied to a non-Map")
    Apply ann (MapPi1 _) xs -> do
      a <- inferType c xs
      case a of
        Map _ n b (Product _ d _) -> return (Map ann n b d)
        _ -> Left (ErrorMessage ann "Map(pi1) applied to a non-Map or a Map whose value type is not a Cartesian product")
    Apply ann (MapPi2 _) xs -> do
      a <- inferType c xs
      case a of
        Map _ n b (Product _ _ d) -> return (Map ann n b d)
        _ -> Left (ErrorMessage ann "Map(pi2) applied to a non-Map or a Map whose value type is not a Cartesian product")
    Apply ann (SumMapLength _) xs -> do
      a <- inferType c xs
      case a of
        Map _ _ _ (List _ _ _) -> return (N ann)
        _ -> Left (ErrorMessage ann "sum.Map(length) applied to a non-Map-of-Lists")
    Apply ann (SumListLookup _ k) xs -> do
      a <- inferType c k
      b <- inferType c xs
      case b of
        List _ _ (Map _ _ a' d) -> do
          checkTypeIsNumeric c d
          checkTypeInclusion c ann a a'
          return d
        _ -> Left (ErrorMessage ann "sum.List(lookup(_)) applied to a non-List-of-Maps")
    -- generic application inference for those cases not covered above
    Apply ann f x -> do
      a <- inferType c f
      case a of
        F _ _ b d -> do
          checkTerm c b x
          return d
        _ -> Left (ErrorMessage ann "function application head does not contain a function")
    Lambda ann varName domain def -> do
      checkType c domain
      c' <- addToContext c (varName, FreeVariable domain)
      codomain <- inferType c' def
      return (F ann Nothing domain codomain)
    Let _ varName varType def body -> do
      checkType c varType
      c' <- addToContext c (varName, Defined varType def)
      inferType c' body
    Equal ann y z -> do
      a <- case inferType c y of
        Left _ -> do
          a <- inferType c z
          checkTerm c a y
          return a
        Right a -> do
          checkTerm c a z
          return a
      checkFiniteDimType c a
      return (Prop ann)
    LessOrEqual ann y z -> do
      a <- case inferType c y of
        Left _ -> do
          a <- inferType c z
          checkTerm c a y
          return a
        Right a -> do
          checkTerm c a z
          return a
      checkTypeIsNumeric c a
      return (Prop ann)
    And ann p q -> do
      checkTerm c (Prop ann) p
      checkTerm c (Prop ann) q
      return (Prop ann)
    Or ann p q -> do
      checkTerm c (Prop ann) p
      checkTerm c (Prop ann) q
      return (Prop ann)
    Not ann p -> do
      checkTerm c (Prop ann) p
      return (Prop ann)
    Implies ann p q -> do
      checkTerm c (Prop ann) p
      checkTerm c (Prop ann) q
      return (Prop ann)
    ForAll ann varName varType varBound p -> do
      checkType c varType
      maybe (pure ()) (checkBound c varType) varBound
      c' <- addToContext c (varName, FreeVariable varType)
      checkTerm c' (Prop ann) p
      return (Prop ann)
    ForSome ann varName varType varBound p -> do
      checkType c varType
      maybe (pure ()) (checkBound c varType) varBound
      c' <- addToContext c (varName, FreeVariable varType)
      checkTerm c' (Prop ann) p
      return (Prop ann)
    _ -> Left (ErrorMessage (termAnnotation t) "could not infer type of term from context")


checkTypeIsNumeric :: Show ann => ValidContext ann -> Type ann -> Either (ErrorMessage ann) ()
checkTypeIsNumeric c t =
  case t of
    N _ -> return ()
    Z _ -> return ()
    Fin _ _ -> return ()
    NamedType ann name -> getNamedType c ann name >>= checkTypeIsNumeric c
    _ -> Left . ErrorMessage (typeAnnotation t) $ "expected a numeric type but got " <> pack (show t)


checkCardinality :: ann -> Cardinality -> Either (ErrorMessage ann) ()
checkCardinality ann (Cardinality n) =
  if n > 0
  then pure ()
  else Left (ErrorMessage ann "type is empty due to a non-positive cardinality")


checkMaybeCardinality :: ann -> Maybe Cardinality -> Either (ErrorMessage ann) ()
checkMaybeCardinality _ Nothing = pure ()
checkMaybeCardinality ann (Just n) = checkCardinality ann n
