{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module OSL.Evaluation (evaluate) where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger)
import Control.Lens ((^.))
import Control.Monad (join)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (pack)
import Data.Tuple (swap)
import OSL.Types.Cardinality (Cardinality (Cardinality))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.OSL (ValidContext, Type, Term (NamedTerm, AddN, MulN, ConstN, AddZ, MulZ, ConstZ, ConstFp, AddFp, MulFp, Cast, ConstFin, ConstF, ConstSet, Inverse, Pair, Pi1, Pi2, Iota1, Iota2, Apply, FunctionProduct, FunctionCoproduct, Lambda, To, From, Let, IsNothing, Just', Nothing'),
  Name, ContextType (Global, Local), Declaration (Defined, Data, FreeVariable), Type (N, Z, Fin, Fp, F, Prop, Product, Coproduct, NamedType, Maybe))
import OSL.Types.Value (Value (Nat, Int, Fp', Fin', Fun, Predicate, Pair', Iota1', Iota2', To', Maybe'', Bool))
import OSL.ValidateContext (checkTerm, inferType, checkTypeInclusion)
import Stark.Types.Scalar (Scalar, integerToScalar)

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
      case t of
        N _ -> pure (Nat yV)
        Z _ -> pure (Int yV)
        Fp _ -> pure (Fp' yV)
        Fin _ _ -> pure (Fin' yV) 
        _ -> Left . ErrorMessage ann $
          "cast only works on basic numeric types"
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
      rec t y $ e <> EvaluationContext (Map.singleton v z')
    Lambda ann _ _ _ -> partialApplication ann
    Apply _ (To ann name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
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
                "From: named type mismatch"
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
    Apply ann (Just' _) y -> do
      case t of
        Maybe _ a ->
          Maybe'' . Just <$> rec a y e
        _ -> Left . ErrorMessage ann $
          "saw just in a non-Maybe context"
    Just' ann -> partialApplication ann
    Nothing' _ -> pure (Maybe'' Nothing)
  where
    rec = evaluate gc lc

    partialApplication ann =
      Left . ErrorMessage ann $
        "encountered a partial application of a primitive function"

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
