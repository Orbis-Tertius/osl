{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module OSL.Evaluation (evaluate) where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger, integerToInt)
import Control.Lens ((^.))
import Control.Monad (join)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (pack)
import Data.Tuple (swap)
import OSL.Types.Cardinality (Cardinality (Cardinality))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.OSL (ValidContext (ValidContext), Type, Term (NamedTerm, AddN, MulN, ConstN, AddZ, MulZ, ConstZ, ConstFp, AddFp, MulFp, Cast, ConstFin, ConstF, ConstSet, Inverse, Pair, Pi1, Pi2, Iota1, Iota2, Apply, FunctionProduct, FunctionCoproduct, Lambda, To, From, Let, IsNothing, Just', Nothing', Maybe', MaybePi1, MaybePi2, MaybeTo, MaybeFrom, MaxN, MaxZ, MaxFp, Exists, Length, Nth, ListCast, ListPi1, ListPi2, ListTo, ListFrom, ListLength, ListMaybePi1, ListMaybePi2, ListMaybeLength),
  Name, ContextType (Global, Local), Declaration (Defined, Data, FreeVariable), Type (N, Z, Fin, Fp, F, Prop, Product, Coproduct, NamedType, Maybe))
import OSL.Types.Value (Value (Nat, Int, Fp', Fin', Fun, Predicate, Pair', Iota1', Iota2', To', Maybe'', Bool, List''))
import OSL.ValidContext (getFreeOSLName)
import OSL.ValidateContext (checkTerm, inferType, checkTypeInclusion)
import Safe (atMay)
import Stark.Types.Scalar (Scalar, integerToScalar, scalarToInteger)

evaluate ::
  Show ann =>
  ValidContext 'Global ann ->
  ValidContext 'Local ann ->
  Type ann ->
  Term ann ->
  EvaluationContext ->
  Either (ErrorMessage ann) Value
evaluate gc lc t x e = do
  checkTerm lc t x
  case x of
    NamedTerm ann name -> evalName gc lc e ann name
    Apply ann (Apply _ (AddN _) y) z ->
      Nat <$>
      (join $ liftMath ann (Group.+)
               <$> rec t y e
               <*> rec t z e)
    Apply ann (Apply _ (MulN _) y) z ->
      Nat <$>
      (join $ liftMath ann (Ring.*)
                <$> rec t y e
                <*> rec t z e)
    ConstN ann y ->
      case integerToScalar y of
        Just y' -> pure (Nat y')
        Nothing -> Left . ErrorMessage ann $
          "constant out of range of scalar field"
    Apply ann (Apply _ (AddZ _) y) z ->
      Int <$>
      (join $ liftMath ann (Group.+)
               <$> rec t y e
               <*> rec t z e)
    Apply ann (Apply _ (MulZ _) y) z ->
      Int <$>
      (join $ liftMath ann (Ring.*)
                <$> rec t y e
                <*> rec t z e)
    ConstZ ann y ->
      case integerToScalar y of
        Just y' -> pure (Int y')
        Nothing -> Left . ErrorMessage ann $
          "constant out of range of scalar field"
    Apply ann (Apply _ (AddFp _) y) z ->
      Fp' <$>
      (join $ liftMath ann (Group.+)
               <$> rec t y e
               <*> rec t z e)
    Apply ann (Apply _ (MulFp _) y) z ->
      Fp' <$>
      (join $ liftMath ann (Ring.*)
               <$> rec t y e
               <*> rec t z e)
    ConstFp ann y ->
      case integerToScalar y of
        Just y' -> pure (Fp' y')
        Nothing -> Left . ErrorMessage ann $
          "constant out of range of scalar field"
    ConstFin ann y ->
      case integerToScalar y of
        Just y' -> pure (Fin' y')
        Nothing -> Left . ErrorMessage ann $
          "constant out of range of scalar field"
    Apply ann (Cast _) y -> do
      yT <- inferType lc y
      yV <- decodeScalar ann =<< rec yT y e
      castF ann yV

    ConstF ann f ->
      case t of
        F _ mn a b -> do
          xs <- mapM (\x' -> rec a x' e) (fst <$> f)
          ys <- mapM (\y' -> rec b y' e) (snd <$> f)
          case mn of
            Just (Cardinality n) ->
              if intToInteger (length f) <= n
              then pure (Fun (Map.fromList (zip xs ys)))
              else Left . ErrorMessage ann $
                "function constant larger than function type cardinality"
            Nothing -> pure (Fun (Map.fromList (zip xs ys)))
        _ -> Left . ErrorMessage ann $
          "encountered a function constant in a non-function context"
    AddN ann -> partialApplication ann
    MulN ann -> partialApplication ann
    AddZ ann -> partialApplication ann
    MulZ ann -> partialApplication ann
    AddFp ann -> partialApplication ann
    MulFp ann -> partialApplication ann
    Cast ann -> partialApplication ann
    ConstSet ann xs ->
      case t of
        F _ mn a (Prop _) -> do
          xs' <- mapM (\x' -> rec a x' e) xs
          case mn of
            Just (Cardinality n) ->
              if intToInteger (length xs) <= n
              then pure (Predicate (Set.fromList xs'))
              else Left . ErrorMessage ann $
                "set constant larger than type cardinality"
            Nothing ->
              pure (Predicate (Set.fromList xs'))
        _ -> Left . ErrorMessage ann $
          "encountered a set constant in a non-predicate context"
    Apply ann (Inverse _) f -> do
      f' <- rec t f e
      case f' of
        Fun f'' ->
          pure (Fun (Map.fromList (swap <$> Map.toList f'')))
        _ ->
          Left . ErrorMessage ann $
            "inverse: expected a function"
    Inverse ann -> partialApplication ann
    Apply ann (Apply _ (Pair _) y) z ->
      case t of
        Product _ a b ->
          Pair' <$> rec a y e <*> rec b z e
        _ ->
          Left . ErrorMessage ann $
            "encountered a pair in a non-product context"
    Pair ann -> partialApplication ann
    Apply ann (Pi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        Pair' z _ -> pure z
        _ -> Left . ErrorMessage ann $
          "pi1: expected a pair"
    Pi1 ann -> partialApplication ann
    Apply ann (Pi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        Pair' _ z -> pure z
        _ -> Left . ErrorMessage ann $
          "pi2: expected a pair"
    Pi2 ann -> partialApplication ann
    Apply ann (Iota1 _) y ->
      case t of
        Coproduct _ a _ ->
          Iota1' <$> rec a y e
        _ ->
          Left . ErrorMessage ann $
            "encountered iota1 in a non-coproduct context"
    Iota1 ann -> partialApplication ann
    Apply ann (Iota2 _) y ->
      case t of
        Coproduct _ _ b ->
          Iota2' <$> rec b y e
        _ ->
          Left . ErrorMessage ann $
            "encountered iota2 in a non-coproduct context"
    Iota2 ann -> partialApplication ann
    FunctionProduct ann f g ->
      case t of
        F ann' n a (Product _ b c) -> do
          f' <- rec (F ann' n a b) f e
          g' <- rec (F ann' n a c) g e
          case (f', g') of
            (Fun f'', Fun g'') ->
              pure . Fun
                $ Map.unionWith Pair' f'' g''
            _ -> Left . ErrorMessage ann $
              "function product arguments expected to be functions"
        _ ->
          Left . ErrorMessage ann $
            "encountered a function product in a non-function-product context"
    FunctionCoproduct ann f g ->
      case t of
        F ann' n (Coproduct _ a b) c -> do
          f' <- rec (F ann' n a c) f e
          g' <- rec (F ann' n b c) g e
          case (f', g') of
            (Fun f'', Fun g'') ->
              pure . Fun
                $ Map.mapKeys Iota1' f'' <>
                  Map.mapKeys Iota2' g''
            _ -> Left . ErrorMessage ann $
             "function coproduct arguments expected to be functions"
        _ -> Left . ErrorMessage ann $
          "encountered a function coproduct in a non-function-coproduct context"
    Apply _ (Lambda _ v a y) z -> do
      z' <- rec a z e
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      evaluate gc lc' t y $ e <> EvaluationContext (Map.singleton v z')
    Lambda ann _ _ _ -> partialApplication ann
    Apply _ (To ann name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) ->
          To' name <$> rec a y e
        _ -> Left . ErrorMessage ann $
          "expected the name of a type"
    To ann _ -> partialApplication ann
    Apply ann (From ann' name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
          checkTypeInclusion lc ann t a
          y' <- rec (NamedType ann name) y e
          case y' of
            To' name' y'' ->
              if name' == name
              then pure y''
              else Left . ErrorMessage ann' $
                "from(-): named type mismatch"
            _ -> Left . ErrorMessage ann' $
              "expected a To value"
        _ -> Left . ErrorMessage ann $
          "expected the name of a type"
    From ann _ -> partialApplication ann
    Let _ v a d y -> do
      d' <- rec a d e
      rec t y $ e <> EvaluationContext (Map.singleton v d')
    Apply ann (IsNothing _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        Maybe'' Nothing -> pure (Bool True)
        Maybe'' (Just _) -> pure (Bool False)
        _ -> Left . ErrorMessage ann $
          "expected a Maybe value"
    IsNothing ann -> partialApplication ann
    Apply ann (Just' _) y ->
      case t of
        Maybe _ a ->
          Maybe'' . Just <$> rec a y e
        _ -> Left . ErrorMessage ann $
          "saw just in a non-Maybe context"
    Just' ann -> partialApplication ann
    Nothing' _ -> pure (Maybe'' Nothing)
    Apply ann (Apply _ (Maybe' ann' f) y) z -> do
      fT <- inferType lc f
      case fT of
        F _ _ a _ -> do
          z' <- rec (Maybe ann' a) z e
          let v = getFreeOSLName lc
          case z' of
             Maybe'' (Just z'') ->
               rec t (Apply ann f (NamedTerm ann v))
                 $ e <> EvaluationContext (Map.singleton v z'')
             Maybe'' Nothing -> rec t y e
             _ -> Left . ErrorMessage ann $
               "maybe: expected a Maybe value"
        _ -> Left . ErrorMessage ann' $
          "maybe: expected a function"
    Maybe' ann _ -> partialApplication ann
    Apply ann (MaybePi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        Maybe'' (Just (Pair' z _)) ->
          pure (Maybe'' (Just z))
        Maybe'' Nothing ->
          pure (Maybe'' Nothing)
        _ -> Left . ErrorMessage ann $
          "Maybe(pi1): expected a Maybe-pair"
    MaybePi1 ann -> partialApplication ann
    Apply ann (MaybePi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        Maybe'' (Just (Pair' _ z)) ->
          pure (Maybe'' (Just z))
        Maybe'' Nothing ->
          pure (Maybe'' Nothing)
        _ -> Left . ErrorMessage ann $
          "Maybe(pi2): expected a Maybe-pair"
    MaybePi2 ann -> partialApplication ann
    Apply ann (MaybeTo ann' name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
          y' <- rec (Maybe ann' a) y e
          case y' of
            Maybe'' (Just y'') ->
              pure (Maybe'' (Just (To' name y'')))
            Maybe'' Nothing ->
              pure (Maybe'' Nothing)
            _ -> Left . ErrorMessage ann $
              "Maybe(to(-)): expected a Maybe"
        _ -> Left . ErrorMessage ann' $
          "expected the name of a type"
    MaybeTo ann _ -> partialApplication ann
    Apply ann (MaybeFrom ann' name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
          checkTypeInclusion lc ann t (Maybe ann' a)
          y' <- rec (Maybe ann' (NamedType ann' name)) y e
          case y' of
            Maybe'' (Just (To' name' y'')) ->
              if name' == name
              then pure (Maybe'' (Just y''))
              else Left . ErrorMessage ann' $
                "Maybe(from(-)): named type mismatch"
            Maybe'' Nothing ->
              pure (Maybe'' Nothing)
            _ -> Left . ErrorMessage ann $
              "expected a Maybe(" <> pack (show name) <> ")"
        _ -> Left . ErrorMessage ann' $
          "expected the name of a type"
    MaybeFrom ann _ -> partialApplication ann
    Apply ann (Apply _ (MaxN _) y) z ->
      Nat <$>
      (join $ liftMath ann max
               <$> rec t y e
               <*> rec t z e)
    MaxN ann -> partialApplication ann
    Apply ann (Apply _ (MaxZ _) y) z ->
      Int <$>
      (join $ liftMath ann max
                <$> rec t y e
                <*> rec t z e)
    MaxZ ann -> partialApplication ann
    Apply ann (Apply _ (MaxFp _) y) z ->
      Fp' <$>
      (join $ liftMath ann max
               <$> rec t y e
               <*> rec t z e)
    MaxFp ann -> partialApplication ann
    Apply ann (Exists _) y -> do
      y' <- rec (Maybe ann t) y e
      case y' of
        Maybe'' (Just y'') -> pure y''
        Maybe'' Nothing -> Left . ErrorMessage ann $
          "applied exists to nothing"
        _ -> Left . ErrorMessage ann $
          "exists: expected a Maybe"
    Exists ann -> partialApplication ann
    Apply ann (Length _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' xs ->
          case integerToScalar (intToInteger (length xs)) of
            Just l -> pure (Nat l)
            Nothing -> Left . ErrorMessage ann $
              "length of list is out of range of scalar field"
        _ -> Left . ErrorMessage ann $
          "length: expected a list"
    Length ann -> partialApplication ann
    Apply ann (Apply _ (Nth _) xs) i -> do
      i' <- rec (N ann) i e
      xsT <- inferType lc xs
      xs' <- rec xsT xs e
      case i' of
        Nat i'' ->
          case integerToInt (scalarToInteger i'') of
            Just i''' ->
              case xs' of
                List'' xs'' ->
                  case xs'' `atMay` i''' of
                    Just y -> pure y
                    Nothing -> Left . ErrorMessage ann $
                      "nth: index out of range"
                _ -> Left . ErrorMessage ann $
                  "nth: expected a list"
            Nothing -> Left . ErrorMessage ann $
              "nth: index out of range of scalar field"
        _ -> Left . ErrorMessage ann $
          "nth: expected a natural number"
    Nth ann -> partialApplication ann
    Apply ann (ListCast _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' xs ->
          List'' <$> mapM ((castF ann =<<) . decodeScalar ann) xs
        _ -> Left . ErrorMessage ann $
          "List(cast): expected a list"
    ListCast ann -> partialApplication ann
    Apply ann (ListPi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' xs -> List'' <$> mapM (fst' ann) xs
        _ -> Left . ErrorMessage ann $ "List(pi1): expected a list"
    ListPi1 ann -> partialApplication ann
    Apply ann (ListPi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' xs -> List'' <$> mapM (snd' ann) xs
        _ -> Left . ErrorMessage ann $ "List(pi2): expected a list"
    ListPi2 ann -> partialApplication ann
    Apply ann (ListTo _ name) y -> do
      yT <- inferType lc y 
      y' <- rec yT y e
      case y' of
        List'' ys -> pure (List'' (To' name <$> ys))
        _ -> Left . ErrorMessage ann $ "List(to(-)): expected a list"
    ListTo ann _ -> partialApplication ann
    Apply ann (ListFrom _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' ys -> List'' <$> mapM (castFrom ann name) ys
        _ -> Left . ErrorMessage ann $ "List(from(-)): expected a list"
    ListFrom ann _ -> partialApplication ann
    Apply ann (ListLength _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' ys -> List'' <$> mapM (listLength ann) ys
        _ -> Left . ErrorMessage ann $ "List(length): expected a list"
    ListLength ann -> partialApplication ann
    Apply ann (ListMaybePi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' ys -> List'' <$> mapM (maybeFunctor fst' ann) ys
        _ -> Left . ErrorMessage ann $ "List(Maybe(pi1)): expected a list"
    Apply ann (ListMaybePi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' ys -> List'' <$> mapM (maybeFunctor snd' ann) ys
        _ -> Left . ErrorMessage ann $ "List(Maybe(pi2)): expected a list"
    Apply ann (ListMaybeLength _) y -> do
      yT <- inferType lc y
      y' <- rec yT y e
      case y' of
        List'' ys -> List'' <$> mapM (maybeFunctor listLength ann) ys
        _ -> Left . ErrorMessage ann $ "List(length): expected a list"
  where
    rec = evaluate gc lc

    listLength :: ann -> Value -> Either (ErrorMessage ann) Value
    listLength ann =
      \case
        List'' ys ->
          case integerToScalar (intToInteger (length ys)) of
            Just l -> pure (Nat l)
            Nothing -> Left . ErrorMessage ann $
              "length of list out of range of scalar field"
        _ -> Left . ErrorMessage ann $ "expected a list"
    castFrom :: ann -> Name -> Value -> Either (ErrorMessage ann) Value
    castFrom ann name =
      \case
        To' name' y ->
          if name == name'
          then pure y
          else Left . ErrorMessage ann $ "from(-): name type mismatch"
        _ -> Left . ErrorMessage ann $ "from(-): expected a To value"

    castF :: ann -> Scalar -> Either (ErrorMessage ann) Value
    castF ann yV =
      case t of
        N _ -> pure (Nat yV)
        Z _ -> pure (Int yV)
        Fp _ -> pure (Fp' yV)
        Fin _ _ -> pure (Fin' yV) 
        _ -> Left . ErrorMessage ann $
          "cast only works on basic numeric types"

    fst' :: ann -> Value -> Either (ErrorMessage ann) Value
    fst' ann =
      \case
        Pair' y _ -> pure y
        _ -> Left . ErrorMessage ann $ "pi1: expected a pair"

    snd' :: ann -> Value -> Either (ErrorMessage ann) Value
    snd' ann =
      \case
        Pair' _ y -> pure y
        _ -> Left . ErrorMessage ann $ "pi2: expected a pair"

    maybeFunctor ::
      (ann -> Value -> Either (ErrorMessage ann) Value) ->
      ann -> Value -> Either (ErrorMessage ann) Value
    maybeFunctor f ann =
      \case
        Maybe'' (Just y) -> f ann y
        Maybe'' Nothing -> pure (Maybe'' Nothing)
        _ -> Left . ErrorMessage ann $ "Maybe functor: expected a Maybe value"

    partialApplication ann =
      Left . ErrorMessage ann $
        "encountered a partial function application"

evalName ::
  Show ann =>
  ValidContext 'Global ann ->
  ValidContext 'Local ann ->
  EvaluationContext ->
  ann ->
  Name ->
  Either (ErrorMessage ann) Value
evalName gc lc e ann name =
  case Map.lookup name (e ^. #unEvaluationContext) of
    Just v -> pure v
    Nothing ->
      case Map.lookup name (lc ^. #unValidContext) of
        Just (Defined u y) -> evaluate gc mempty u y mempty
        Just (FreeVariable _) -> Left . ErrorMessage ann $
          "undefined free variable"
        Just (Data _) -> Left . ErrorMessage ann $
          "expected a term denoting a value"
        Nothing -> Left . ErrorMessage ann $
          "undefined name: " <> pack (show name)

liftMath :: ann -> (Scalar -> Scalar -> a) -> Value -> Value -> Either (ErrorMessage ann) a
liftMath ann f x y =
  f <$> decodeScalar ann x <*> decodeScalar ann y

todo :: a
todo = todo

decodeScalar :: ann -> Value -> Either (ErrorMessage ann) Scalar
decodeScalar = todo
