{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module OSL.Evaluation (evaluate) where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger, integerToInt)
import Control.Lens ((^.))
import Control.Monad (join, liftM2, (<=<))
import Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (pack)
import Data.Tuple (swap)
import Die (die)
import OSL.Bound (boundAnnotation)
import OSL.Term (termAnnotation)
import OSL.Types.Argument (Witness (Witness))
import OSL.Types.Cardinality (Cardinality (Cardinality))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.OSL
  ( Bound (CoproductBound, FieldMaxBound, MaybeBound, ProductBound, ScalarBound, ToBound),
    ContextType (Global, Local),
    Declaration (Data, Defined, FreeVariable),
    LeftBound (LeftBound),
    Name,
    RightBound (RightBound),
    Term (AddFp, AddN, AddZ, And, Apply, Bottom, Cast, ConstF, ConstFin, ConstFp, ConstN, ConstSet, ConstZ, Equal, Exists, ForAll, ForSome, From, FunctionCoproduct, FunctionProduct, Iff, Implies, Inverse, Iota1, Iota2, IsNothing, Just', Keys, Lambda, Length, LessOrEqual, Let, ListCast, ListFrom, ListLength, ListMaybeFrom, ListMaybeLength, ListMaybePi1, ListMaybePi2, ListMaybeTo, ListPi1, ListPi2, ListTo, Lookup, MapFrom, MapPi1, MapPi2, MapTo, MaxFp, MaxN, MaxZ, Maybe', MaybeFrom, MaybePi1, MaybePi2, MaybeTo, MulFp, MulN, MulZ, NamedTerm, Not, Nothing', Nth, Or, Pair, Pi1, Pi2, Sum, SumListLookup, SumMapLength, To, Top),
    Type (Coproduct, F, Fin, Fp, List, Map, Maybe, N, NamedType, P, Product, Prop, Z),
    ValidContext (ValidContext),
    ValuesBound (ValuesBound),
  )
import OSL.Types.PreValue (PreValue (LambdaClosure, PreIota1, PreIota2, PrePair, PreTo, Value))
import OSL.Types.Value (Value (Bool, Fin', Fp', Fun, Int, Iota1', Iota2', List'', Map'', Maybe'', Nat, Pair', Predicate, To'))
import OSL.ValidContext (getFreeOSLName)
import OSL.ValidateContext (checkTerm, checkTypeInclusion, inferType)
import OSL.Witness (splitWitness)
import Safe (atMay)
import Stark.Types.Scalar (Scalar, integerToScalar, scalarToInteger, zero)

evaluate ::
  Show ann =>
  ValidContext 'Global ann ->
  ValidContext 'Local ann ->
  Type ann ->
  Term ann ->
  Witness ->
  EvaluationContext ann ->
  Either (ErrorMessage ann) Value
evaluate gc lc t x w e = do
  preValueToValue (termAnnotation x)
    =<< evaluate' gc lc t x w e

preValueToValue ::
  ann ->
  PreValue ann ->
  Either (ErrorMessage ann) Value
preValueToValue ann =
  \case
    Value x -> pure x
    LambdaClosure _ ->
      Left . ErrorMessage ann $
        "expected a value but got a lambda closure"
    PrePair x y ->
      Pair' <$> rec x <*> rec y
    PreTo name x ->
      To' name <$> rec x
    PreIota1 x ->
      Iota1' <$> rec x
    PreIota2 x ->
      Iota2' <$> rec x
  where
    rec = preValueToValue ann

evaluate' ::
  Show ann =>
  ValidContext 'Global ann ->
  ValidContext 'Local ann ->
  Type ann ->
  Term ann ->
  Witness ->
  EvaluationContext ann ->
  Either (ErrorMessage ann) (PreValue ann)
evaluate' gc lc t x w e = do
  checkTerm lc t x
  case x of
    NamedTerm ann name ->
      evalName gc lc e ann name w
    Apply ann (Apply _ (AddN _) y) z ->
      Value . Nat
        <$> join
          ( liftMath ann (Group.+)
              <$> rec t y w e
              <*> rec t z w e
          )
    Apply ann (Apply _ (MulN _) y) z ->
      Value . Nat
        <$> join
          ( liftMath ann (Ring.*)
              <$> rec t y w e
              <*> rec t z w e
          )
    ConstN ann y ->
      case integerToScalar y of
        Just y' -> pure (Value (Nat y'))
        Nothing ->
          Left . ErrorMessage ann $
            "constant out of range of scalar field"
    Apply ann (Apply _ (AddZ _) y) z ->
      Value . Int
        <$> join
          ( liftMath ann (Group.+)
              <$> rec t y w e
              <*> rec t z w e
          )
    Apply ann (Apply _ (MulZ _) y) z ->
      Value . Int
        <$> join
          ( liftMath ann (Ring.*)
              <$> rec t y w e
              <*> rec t z w e
          )
    ConstZ ann y ->
      case integerToScalar y of
        Just y' -> pure (Value (Int y'))
        Nothing ->
          Left . ErrorMessage ann $
            "constant out of range of scalar field"
    Apply ann (Apply _ (AddFp _) y) z ->
      Value . Fp'
        <$> join
          ( liftMath ann (Group.+)
              <$> rec t y w e
              <*> rec t z w e
          )
    Apply ann (Apply _ (MulFp _) y) z ->
      Value . Fp'
        <$> join
          ( liftMath ann (Ring.*)
              <$> rec t y w e
              <*> rec t z w e
          )
    ConstFp ann y ->
      case integerToScalar y of
        Just y' -> pure (Value (Fp' y'))
        Nothing ->
          Left . ErrorMessage ann $
            "constant out of range of scalar field"
    ConstFin ann y ->
      case integerToScalar y of
        Just y' -> pure (Value (Fin' y'))
        Nothing ->
          Left . ErrorMessage ann $
            "constant out of range of scalar field"
    Apply ann (Cast _) y -> do
      yT <- inferType lc y
      yV <- decodeScalar ann =<< rec yT y w e
      Value <$> castF ann yV
    ConstF ann f ->
      case t of
        F _ mn a b -> do
          xs <- mapM (\x' -> rec a x' w e) (fst <$> f)
          ys <- mapM (\y' -> rec b y' w e) (snd <$> f)
          case mn of
            Just (Cardinality n) ->
              if intToInteger (length f) <= n
                then pure (Value (Fun (Map.fromList (zip xs ys))))
                else
                  Left . ErrorMessage ann $
                    "function constant larger than function type cardinality"
            Nothing -> pure (Value (Fun (Map.fromList (zip xs ys))))
        _ ->
          Left . ErrorMessage ann $
            "encountered a function constant in a non-function context"
    AddN ann -> partialApplication "AddN" ann
    MulN ann -> partialApplication "MulN" ann
    AddZ ann -> partialApplication "AddZ" ann
    MulZ ann -> partialApplication "MulZ" ann
    AddFp ann -> partialApplication "AddFp" ann
    MulFp ann -> partialApplication "MulFp" ann
    Cast ann -> partialApplication "Cast" ann
    ConstSet ann xs ->
      case t of
        F _ mn a (Prop _) -> do
          xs' <- mapM (\x' -> rec a x' w e) xs
          case mn of
            Just (Cardinality n) ->
              if intToInteger (length xs) <= n
                then pure (Value (Predicate (Set.fromList xs')))
                else
                  Left . ErrorMessage ann $
                    "set constant larger than type cardinality"
            Nothing ->
              pure (Value (Predicate (Set.fromList xs')))
        _ ->
          Left . ErrorMessage ann $
            "encountered a set constant in a non-predicate context"
    Apply ann (Inverse _) f -> do
      f' <- rec t f w e
      case f' of
        Fun f'' ->
          pure (Value (Fun (Map.fromList (swap <$> Map.toList f''))))
        _ ->
          Left . ErrorMessage ann $
            "inverse: expected a function"
    Inverse ann -> partialApplication "Inverse" ann
    Apply ann (Apply _ (Pair _) y) z ->
      case t of
        Product _ a b ->
          PrePair <$> rec' a y w e <*> rec' b z w e
        _ ->
          Left . ErrorMessage ann $
            "encountered a pair in a non-product context"
    Pair ann -> partialApplication "Pair" ann
    Apply ann (Pi1 _) y -> do
      yT <- inferType lc y
      y' <- rec' yT y w e
      case y' of
        Value (Pair' z _) -> pure (Value z)
        PrePair z _ -> pure z
        _ ->
          Left . ErrorMessage ann $
            "pi1: expected a pair"
    Pi1 ann -> partialApplication "Pi1" ann
    Apply ann (Pi2 _) y -> do
      yT <- inferType lc y
      y' <- rec' yT y w e
      case y' of
        Value (Pair' _ z) -> pure (Value z)
        PrePair _ z -> pure z
        _ ->
          Left . ErrorMessage ann $
            "pi2: expected a pair"
    Pi2 ann -> partialApplication "Pi2" ann
    Apply ann (Iota1 _) y ->
      case t of
        Coproduct _ a _ ->
          PreIota1 <$> rec' a y w e
        _ ->
          Left . ErrorMessage ann $
            "encountered iota1 in a non-coproduct context"
    Iota1 ann -> partialApplication "Iota1" ann
    Apply ann (Iota2 _) y ->
      case t of
        Coproduct _ _ b ->
          PreIota2 <$> rec' b y w e
        _ ->
          Left . ErrorMessage ann $
            "encountered iota2 in a non-coproduct context"
    Iota2 ann -> partialApplication "Iota2" ann
    FunctionProduct ann f g ->
      case t of
        F ann' n a (Product _ b c) -> do
          f' <- rec' (F ann' n a b) f w e
          g' <- rec' (F ann' n a c) g w e
          case (f', g') of
            (Value (Fun f''), Value (Fun g'')) ->
              pure . Value . Fun $
                Map.unionWith Pair' f'' g''
            (LambdaClosure f'', LambdaClosure g'') ->
              pure . LambdaClosure $
                \y -> PrePair <$> f'' y <*> g'' y
            (LambdaClosure f'', Value (Fun g'')) ->
              pure . LambdaClosure $
                \y -> PrePair <$> f'' y <*> (Value <$> applyFun ann (Fun g'') y)
            (Value (Fun f''), LambdaClosure g'') ->
              pure . LambdaClosure $
                \y -> PrePair <$> (Value <$> applyFun ann (Fun f'') y) <*> g'' y
            _ ->
              Left . ErrorMessage ann $
                "function product arguments expected to be functions"
        _ ->
          Left . ErrorMessage ann $
            "encountered a function product in a non-function-product context"
    FunctionCoproduct ann f g ->
      case t of
        F ann' n (Coproduct _ a b) c -> do
          f' <- rec' (F ann' n a c) f w e
          g' <- rec' (F ann' n b c) g w e
          case (f', g') of
            (Value (Fun f''), Value (Fun g'')) ->
              pure . Value . Fun $
                Map.mapKeys Iota1' f''
                  <> Map.mapKeys Iota2' g''
            (LambdaClosure f'', LambdaClosure g'') ->
              pure . LambdaClosure $
                \case
                  Value (Iota1' y) -> f'' (Value y)
                  Value (Iota2' y) -> g'' (Value y)
                  PreIota1 y -> f'' y
                  PreIota2 y -> g'' y
                  _ ->
                    Left . ErrorMessage ann $
                      "expected a coproduct value in function coproduct application"
            (Value (Fun f''), LambdaClosure g'') ->
              pure . LambdaClosure $
                \case
                  Value (Iota1' y) -> Value <$> applyFun ann (Fun f'') (Value y)
                  PreIota1 y -> Value <$> applyFun ann (Fun f'') y
                  Value (Iota2' y) -> g'' (Value y)
                  PreIota2 y -> g'' y
                  _ ->
                    Left . ErrorMessage ann $
                      "expected a coproduct value in function coproduct application"
            (LambdaClosure f'', Value (Fun g'')) ->
              pure . LambdaClosure $
                \case
                  Value (Iota1' y) -> f'' (Value y)
                  Value (Iota2' y) -> Value <$> applyFun ann (Fun g'') (Value y)
                  PreIota1 y -> f'' y
                  PreIota2 y -> Value <$> applyFun ann (Fun g'') y
                  _ ->
                    Left . ErrorMessage ann $
                      "expected a coproduct value in function coproduct application"
            _ ->
              Left . ErrorMessage ann $
                "function coproduct arguments expected to be functions"
        _ ->
          Left . ErrorMessage ann $
            "encountered a function coproduct in a non-function-coproduct context"
    Apply _ (Lambda _ v a y) z -> do
      z' <- rec' a z w e
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      let e' = e <> EvaluationContext (Map.singleton v z')
      evaluate' gc lc' t y w e'
    Lambda ann v a body ->
      case t of
        F _ _ _ b ->
          pure . LambdaClosure $
            \y ->
              evaluate'
                gc
                (lc <> ValidContext (Map.singleton v (FreeVariable a)))
                b
                body
                w
                (e <> EvaluationContext (Map.singleton v y))
        _ ->
          Left . ErrorMessage ann $
            "encountered a lambda in a non-function context"
    Apply _ (To ann name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) ->
          PreTo name <$> rec' a y w e
        _ ->
          Left . ErrorMessage ann $
            "expected the name of a type"
    To ann _ -> partialApplication "To" ann
    Apply ann (From ann' name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
          checkTypeInclusion lc ann t a
          y' <- rec' (NamedType ann name) y w e
          case y' of
            PreTo name' y'' ->
              if name' == name
                then pure y''
                else Left . ErrorMessage ann' $ "from(-): named type mismatch"
            Value (To' name' y'') ->
              if name' == name
                then pure (Value y'')
                else
                  Left . ErrorMessage ann' $
                    "from(-): named type mismatch"
            _ ->
              Left . ErrorMessage ann' $
                "expected a To value"
        _ ->
          Left . ErrorMessage ann $
            "expected the name of a type"
    From ann _ -> partialApplication "From" ann
    Let ann v a d y -> do
      (w0, w1) <- splitWitness ann w
      d' <- rec' a d w0 e
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      let e' = e <> EvaluationContext (Map.singleton v d')
      evaluate' gc lc' t y w1 e'
    Apply ann (IsNothing _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case y' of
        Maybe'' Nothing -> pure (Value (Bool True))
        Maybe'' (Just _) -> pure (Value (Bool False))
        _ ->
          Left . ErrorMessage ann $
            "expected a Maybe value"
    IsNothing ann -> partialApplication "IsNothing" ann
    Apply ann (Just' _) y ->
      case t of
        Maybe _ a ->
          Value . Maybe'' . Just <$> rec a y w e
        _ ->
          Left . ErrorMessage ann $
            "saw just in a non-Maybe context"
    Just' ann -> partialApplication "Just'" ann
    Nothing' _ -> pure (Value (Maybe'' Nothing))
    Apply ann (Apply _ (Maybe' ann' f) y) z -> do
      fT <- inferType lc f
      case fT of
        F _ _ a _ -> do
          z' <- rec (Maybe ann' a) z w e
          let v = getFreeOSLName lc
          case z' of
            Maybe'' (Just z'') ->
              rec' t (Apply ann f (NamedTerm ann v)) w $
                e <> EvaluationContext (Map.singleton v (Value z''))
            Maybe'' Nothing -> rec' t y w e
            _ ->
              Left . ErrorMessage ann $
                "maybe: expected a Maybe value"
        _ ->
          Left . ErrorMessage ann' $
            "maybe: expected a function"
    Maybe' ann _ -> partialApplication "Maybe'" ann
    Apply ann (MaybePi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case y' of
        Maybe'' (Just (Pair' z _)) ->
          pure (Value (Maybe'' (Just z)))
        Maybe'' Nothing ->
          pure (Value (Maybe'' Nothing))
        _ ->
          Left . ErrorMessage ann $
            "Maybe(pi1): expected a Maybe-pair"
    MaybePi1 ann -> partialApplication "MaybePi1" ann
    Apply ann (MaybePi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case y' of
        Maybe'' (Just (Pair' _ z)) ->
          pure (Value (Maybe'' (Just z)))
        Maybe'' Nothing ->
          pure (Value (Maybe'' Nothing))
        _ ->
          Left . ErrorMessage ann $
            "Maybe(pi2): expected a Maybe-pair"
    MaybePi2 ann -> partialApplication "MaybePi2" ann
    Apply ann (MaybeTo ann' name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
          y' <- rec (Maybe ann' a) y w e
          case y' of
            Maybe'' (Just y'') ->
              pure (Value (Maybe'' (Just (To' name y''))))
            Maybe'' Nothing ->
              pure (Value (Maybe'' Nothing))
            _ ->
              Left . ErrorMessage ann $
                "Maybe(to(-)): expected a Maybe"
        _ ->
          Left . ErrorMessage ann' $
            "expected the name of a type"
    MaybeTo ann _ -> partialApplication "MaybeTo" ann
    Apply ann (MaybeFrom ann' name) y ->
      case Map.lookup name (gc ^. #unValidContext) of
        Just (Data a) -> do
          checkTypeInclusion lc ann t (Maybe ann' a)
          y' <- rec (Maybe ann' (NamedType ann' name)) y w e
          case y' of
            Maybe'' (Just (To' name' y'')) ->
              if name' == name
                then pure (Value (Maybe'' (Just y'')))
                else
                  Left . ErrorMessage ann' $
                    "Maybe(from(-)): named type mismatch"
            Maybe'' Nothing ->
              pure (Value (Maybe'' Nothing))
            _ ->
              Left . ErrorMessage ann $
                "expected a Maybe(" <> pack (show name) <> ")"
        _ ->
          Left . ErrorMessage ann' $
            "expected the name of a type"
    MaybeFrom ann _ -> partialApplication "MaybeFrom" ann
    Apply ann (Apply _ (MaxN _) y) z ->
      Value . Nat
        <$> join
          ( liftMath ann max
              <$> rec t y w e
              <*> rec t z w e
          )
    MaxN ann -> partialApplication "MaxN" ann
    Apply ann (Apply _ (MaxZ _) y) z ->
      Value . Int
        <$> join
          ( liftMath ann max
              <$> rec t y w e
              <*> rec t z w e
          )
    MaxZ ann -> partialApplication "MaxZ" ann
    Apply ann (Apply _ (MaxFp _) y) z ->
      Value . Fp'
        <$> join
          ( liftMath ann max
              <$> rec t y w e
              <*> rec t z w e
          )
    MaxFp ann -> partialApplication "MaxFp" ann
    Apply ann (Exists _) y -> do
      y' <- rec (Maybe ann t) y w e
      case y' of
        Maybe'' (Just y'') -> pure (Value y'')
        Maybe'' Nothing ->
          Left . ErrorMessage ann $
            "applied exists to nothing"
        _ ->
          Left . ErrorMessage ann $
            "exists: expected a Maybe"
    Exists ann -> partialApplication "Exists" ann
    Apply ann (Length _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case y' of
        List'' xs ->
          case integerToScalar (intToInteger (length xs)) of
            Just l -> pure (Value (Nat l))
            Nothing ->
              Left . ErrorMessage ann $
                "length of list is out of range of scalar field"
        _ ->
          Left . ErrorMessage ann $
            "length: expected a list"
    Length ann -> partialApplication "Length" ann
    Apply ann (Apply _ (Nth _) xs) i -> do
      i' <- rec (N ann) i w e
      xsT <- inferType lc xs
      xs' <- rec xsT xs w e
      case i' of
        Nat i'' ->
          case integerToInt (scalarToInteger i'') of
            Just i''' ->
              case xs' of
                List'' xs'' ->
                  case xs'' `atMay` i''' of
                    Just y -> pure (Value y)
                    Nothing ->
                      Left . ErrorMessage ann $
                        "nth: index out of range"
                _ ->
                  Left . ErrorMessage ann $
                    "nth: expected a list"
            Nothing ->
              Left . ErrorMessage ann $
                "nth: index out of range of scalar field"
        _ ->
          Left . ErrorMessage ann $
            "nth: expected a natural number"
    Nth ann -> partialApplication "Nth" ann
    Apply ann (ListCast _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (\ann' -> castF ann' <=< decodeScalar ann') ann y'
    ListCast ann -> partialApplication "ListCast" ann
    Apply ann (ListPi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor snd' ann y'
    ListPi1 ann -> partialApplication "ListPi1" ann
    Apply ann (ListPi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor snd' ann y'
    ListPi2 ann -> partialApplication "ListPi2" ann
    Apply ann (ListTo _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (const (pure . To' name)) ann y'
    ListTo ann _ -> partialApplication "ListTo" ann
    Apply ann (ListFrom _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case y' of
        List'' ys -> Value . List'' <$> mapM (castFrom ann name) ys
        _ -> Left . ErrorMessage ann $ "List(from(-)): expected a list"
    ListFrom ann _ -> partialApplication "ListFrom" ann
    Apply ann (ListLength _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor listLength ann y'
    ListLength ann -> partialApplication "ListLength" ann
    Apply ann (ListMaybePi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (maybeFunctor fst') ann y'
    ListMaybePi1 ann -> partialApplication "ListMaybePi1" ann
    Apply ann (ListMaybePi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (maybeFunctor snd') ann y'
    ListMaybePi2 ann -> partialApplication "ListMaybePi2" ann
    Apply ann (ListMaybeLength _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (maybeFunctor listLength) ann y'
    ListMaybeLength ann -> partialApplication "ListMaybeLength" ann
    Apply ann (ListMaybeFrom _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (maybeFunctor (`castFrom` name)) ann y'
    ListMaybeFrom ann _ -> partialApplication "ListMaybeFrom" ann
    Apply ann (ListMaybeTo _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> listFunctor (maybeFunctor (const (pure . To' name))) ann y'
    ListMaybeTo ann _ -> partialApplication "ListMaybeTo" ann
    Apply ann (Sum _) y -> do
      yT <- inferType lc y
      Value <$> (listSum ann =<< rec yT y w e)
    Sum ann -> partialApplication "Sum" ann
    Apply ann (Apply _ (Lookup _) k) m -> do
      mT <- inferType lc m
      m' <- rec mT m w e
      kT <- inferType lc k
      k' <- rec kT k w e
      Value <$> mapLookup ann k' m'
    Lookup ann -> partialApplication "Lookup" ann
    Apply ann (Keys _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case y' of
        Map'' y'' -> pure (Value (List'' (Map.keys y'')))
        _ ->
          Left . ErrorMessage ann $
            "keys: expected a map"
    Keys ann -> partialApplication "Keys" ann
    Apply ann (MapPi1 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> mapFunctor fst' ann y'
    MapPi1 ann -> partialApplication "MapPi1" ann
    Apply ann (MapPi2 _) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> mapFunctor snd' ann y'
    MapPi2 ann -> partialApplication "MapPi2" ann
    Apply ann (MapTo _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> mapFunctor (const (pure . To' name)) ann y'
    MapTo ann _ -> partialApplication "MapTo" ann
    Apply ann (MapFrom _ name) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> mapFunctor (`castFrom` name) ann y'
    MapFrom ann _ -> partialApplication "MapFrom" ann
    Apply ann (SumMapLength _) y -> do
      yT <- inferType lc y
      Value
        <$> ( listSum ann . List'' =<< mapElems ann
                =<< mapFunctor listLength ann
                =<< rec yT y w e
            )
    SumMapLength ann -> partialApplication "SumMapLength" ann
    Apply ann (SumListLookup _ k) y -> do
      yT <- inferType lc y
      y' <- rec yT y w e
      case yT of
        List _ _ (Map _ _ a _) -> do
          k' <- rec a k w e
          Value <$> (listSum ann =<< listFunctor (`mapLookup` k') ann y')
        _ ->
          Left . ErrorMessage ann $
            "sumListLookup: expected a list of maps"
    SumListLookup ann _ -> partialApplication "SumListLookup" ann
    Equal _ y z -> do
      yT <- inferType lc y
      Value . Bool <$> ((==) <$> rec yT y w e <*> rec yT z w e)
    LessOrEqual _ y z -> do
      yT <- inferType lc y
      Value . Bool <$> ((<=) <$> rec yT y w e <*> rec yT z w e)
    And ann p q -> do
      (w0, w1) <- splitWitness ann w
      fmap Value . join $
        liftM2
          (liftLogic ann (&&))
          (rec (Prop ann) p w0 e)
          (rec (Prop ann) q w1 e)
    Or ann p q -> do
      (w0, w1) <- splitWitness ann w
      fmap Value . join $
        liftM2
          (liftLogic ann (||))
          (rec (Prop ann) p w0 e)
          (rec (Prop ann) q w1 e)
    Not ann p -> do
      p' <- rec (Prop ann) p w e
      case p' of
        Bool y -> pure (Value (Bool (not y)))
        _ ->
          Left . ErrorMessage ann $
            "expected a boolean value"
    Implies ann p q -> do
      (w0, w1) <- splitWitness ann w
      fmap Value . join $
        liftM2
          (liftLogic ann (\p' q' -> not p' || q'))
          (rec (Prop ann) p w0 e)
          (rec (Prop ann) q w1 e)
    Iff ann p q -> do
      (w0, w1) <- splitWitness ann w
      fmap Value . join $
        liftM2
          (liftLogic ann (==))
          (rec (Prop ann) p w0 e)
          (rec (Prop ann) q w1 e)
    Top _ -> pure (Value (Bool True))
    Bottom _ -> pure (Value (Bool True))
    Apply ann (NamedTerm ann' fName) y -> do
      case Map.lookup fName (e ^. #unEvaluationContext) of
        Just (Value (Fun f)) -> do
          yT <- inferType lc y
          y' <- rec yT y w e
          case Map.lookup y' f of
            Just v -> pure (Value v)
            Nothing ->
              Left . ErrorMessage ann $
                "input not in function domain: "
                  <> pack (show (y', f))
        Just (LambdaClosure f) -> do
          yT <- inferType lc y
          f =<< rec' yT y w e
        Just _ ->
          Left . ErrorMessage ann $
            "apply: expected a function"
        Nothing ->
          case Map.lookup fName (gc ^. #unValidContext) of
            Just (Defined (F _ann _n a _b) def) -> do
              yT <- inferType lc y
              y' <- rec' yT y w e
              let v = getFreeOSLName gc
              evaluate'
                gc
                (gcAsLc <> ValidContext (Map.singleton v (FreeVariable a)))
                t
                (Apply ann def (NamedTerm ann v))
                w
                ( EvaluationContext
                    (Map.singleton v y')
                )
            Just _ ->
              Left . ErrorMessage ann' $
                "expected the name of a defined function"
            Nothing ->
              Left . ErrorMessage ann' $
                "undefined name"
    ForSome ann name a _bound y -> do
      -- TODO: check w is in bound
      (Witness w0, w1) <- splitWitness ann w
      evaluate'
        gc
        (lc <> ValidContext (Map.singleton name (FreeVariable a)))
        (Prop ann)
        y
        w1
        ( e
            <> EvaluationContext
              (Map.singleton name (Value w0))
        )
    ForAll ann name a bound y -> do
      vs <- getUniversalQuantifierValues a bound
      let lc' = lc <> ValidContext (Map.singleton name (FreeVariable a))
          p v = do
            w' <- Witness <$> applyFunWithDefault ann (w ^. #unWitness) (Value v) (Fin' 0)
            decodeBool ann <=< evaluate gc lc' (Prop ann) y w' . (e <>) . EvaluationContext $
              Map.singleton name (Value v)
      Value . Bool . and <$> mapM p vs
    Apply ann (AddN _) _ -> partialApplication "AddN _" ann
    Apply ann (MulN _) _ -> partialApplication "MulN _" ann
    Apply ann (ConstN _ _) _ -> expectedFunction ann
    Apply ann (AddZ _) _ -> partialApplication "AddZ _" ann
    Apply ann (MulZ _) _ -> partialApplication "MulZ _" ann
    Apply ann (ConstZ _ _) _ -> expectedFunction ann
    Apply ann (ConstFp _ _) _ -> expectedFunction ann
    Apply ann (AddFp _) _ -> partialApplication "AddFp _" ann
    Apply ann (MulFp _) _ -> partialApplication "MulFp _" ann
    Apply ann (ConstFin _ _) _ -> expectedFunction ann
    Apply _ fE@(ConstF ann' _) y -> do
      fT <- inferType lc fE
      f <- rec fT fE w e
      yT <- inferType lc y
      y' <- rec yT y w e
      Value <$> applyFun ann' f (Value y')
    Apply _ sE@(ConstSet ann' _) y -> do
      sT <- inferType lc sE
      s <- rec sT sE w e
      yT <- inferType lc y
      y' <- rec yT y w e
      case s of
        Predicate s' ->
          pure (Value (Bool (y' `Set.member` s')))
        _ ->
          Left . ErrorMessage ann' $
            "expected a set"
    Apply ann (Pair _) _ -> partialApplication "Pair _" ann
    Apply ann fE@(FunctionProduct {}) y -> do
      fT <- inferType lc fE
      f <- rec' fT fE w e
      yT <- inferType lc y
      y' <- rec' yT y w e
      applyF ann f y'
    Apply ann fE@(FunctionCoproduct {}) y -> do
      fT <- inferType lc fE
      f <- rec' fT fE w e
      yT <- inferType lc y
      y' <- rec' yT y w e
      applyF ann f y'
    Apply ann fE@(Let {}) y -> do
      fT <- inferType lc fE
      f <- rec' fT fE w e
      yT <- inferType lc y
      y' <- rec' yT y w e
      applyF ann f y'
    -- NOTICE: this catch-all case must come after all other Apply Apply cases
    Apply ann fE@(Apply {}) y -> do
      fT <- inferType lc fE
      f <- rec' fT fE w e
      yT <- inferType lc y
      y' <- rec' yT y w e
      applyF ann f y'
    Apply ann (Nothing' _) _ -> expectedFunction ann
    Apply ann (Maybe' {}) _ -> partialApplication "Maybe _" ann
    Apply ann (MaxN _) _ -> partialApplication "MaxN _" ann
    Apply ann (MaxZ _) _ -> partialApplication "MaxZ _" ann
    Apply ann (MaxFp _) _ -> partialApplication "MaxFp _" ann
    Apply ann (Nth _) _ -> partialApplication "Nth _" ann
    Apply ann (Lookup _) _ -> partialApplication "Lookup _" ann
    Apply ann (Equal {}) _ -> expectedFunction ann
    Apply ann (LessOrEqual {}) _ -> expectedFunction ann
    Apply ann (And {}) _ -> expectedFunction ann
    Apply ann (Or {}) _ -> expectedFunction ann
    Apply ann (Not {}) _ -> expectedFunction ann
    Apply ann (Implies {}) _ -> expectedFunction ann
    Apply ann (Iff {}) _ -> expectedFunction ann
    Apply ann (ForAll {}) _ -> expectedFunction ann
    Apply ann (ForSome {}) _ -> expectedFunction ann
    Apply ann (Top _) _ -> expectedFunction ann
    Apply ann (Bottom _) _ -> expectedFunction ann
  where
    rec' = evaluate' gc lc

    rec = evaluate gc lc

    gcAsLc = ValidContext (gc ^. #unValidContext)

    -- getUniversalQuantifierValues :: Type ann -> Maybe (Bound ann) -> Either (ErrorMessage ann) [Value]
    getUniversalQuantifierValues =
      \case
        Prop ann ->
          const . Left . ErrorMessage ann $
            "quantification over Prop not supported"
        F ann _ _ _ ->
          const . Left . ErrorMessage ann $
            "universal quantification over functions not supported"
        P ann _ _ _ ->
          const . Left . ErrorMessage ann $
            "quantification over predicates not supported"
        N ann ->
          \case
            Nothing ->
              Left . ErrorMessage ann $
                "universal quantification over N requires a bound"
            Just (ScalarBound ann' bound) -> do
              bound' <- decodeScalar ann' =<< rec (N ann') bound (Witness (Fin' 0)) e
              pure (Nat . integerToScalarUnsafe <$> [0 .. scalarToInteger bound' - 1])
            Just (FieldMaxBound ann') ->
              Left . ErrorMessage ann' $ "field max bound is not allowed for universal quantifiers"
            Just b -> Left . ErrorMessage (boundAnnotation b) $ "bound type mismatch"
        Z ann ->
          \case
            Nothing ->
              Left . ErrorMessage ann $
                "universal quantification over Z requires a bound"
            Just (ScalarBound ann' bound) -> do
              bound' <- decodeScalar ann' =<< rec (Z ann') bound (Witness (Fin' 0)) e
              pure (Int . integerToScalarUnsafe <$> [0 .. scalarToInteger bound' - 1])
            Just (FieldMaxBound ann') ->
              Left . ErrorMessage ann' $ "field max bound is not allowed for universal quantifiers"
            Just b -> Left . ErrorMessage (boundAnnotation b) $ "bound type mismatch"
        Fp ann ->
          \case
            Nothing ->
              Left . ErrorMessage ann $
                "universal quantification over F requires a bound"
            Just (ScalarBound ann' bound) -> do
              bound' <- decodeScalar ann' =<< rec (Fp ann') bound (Witness (Fin' 0)) e
              pure (Fp' . integerToScalarUnsafe <$> [0 .. scalarToInteger bound' - 1])
            Just (FieldMaxBound ann') ->
              Left . ErrorMessage ann' $ "field max bound is not allowed for universal quantifiers"
            Just b -> Left . ErrorMessage (boundAnnotation b) $ "bound type mismatch"
        Fin _ n ->
          \case
            Nothing ->
              pure (Fin' . integerToScalarUnsafe <$> [0 .. n - 1])
            Just (ScalarBound ann' bound) -> do
              bound' <- decodeScalar ann' =<< rec (Fin ann' n) bound (Witness (Fin' 0)) e
              pure (Fin' . integerToScalarUnsafe <$> [0 .. scalarToInteger bound' - 1])
            Just b -> Left . ErrorMessage (boundAnnotation b) $ "bound type mismatch"
        Product _ a b ->
          \case
            Nothing -> do
              aVs <- getUniversalQuantifierValues a Nothing
              bVs <- getUniversalQuantifierValues b Nothing
              pure [Pair' aV bV | aV <- aVs, bV <- bVs]
            Just (ProductBound _ (LeftBound aBound) (RightBound bBound)) -> do
              aVs <- getUniversalQuantifierValues a (Just aBound)
              bVs <- getUniversalQuantifierValues b (Just bBound)
              pure [Pair' aV bV | aV <- aVs, bV <- bVs]
            Just bound ->
              Left . ErrorMessage (boundAnnotation bound) $
                "bound type mismatch"
        Coproduct _ a b ->
          \case
            Nothing -> do
              aVs <- getUniversalQuantifierValues a Nothing
              bVs <- getUniversalQuantifierValues b Nothing
              pure $ (Iota1' <$> aVs) <> (Iota2' <$> bVs)
            Just (CoproductBound _ (LeftBound aBound) (RightBound bBound)) -> do
              aVs <- getUniversalQuantifierValues a (Just aBound)
              bVs <- getUniversalQuantifierValues b (Just bBound)
              pure $ (Iota1' <$> aVs) <> (Iota2' <$> bVs)
            Just bound ->
              Left . ErrorMessage (boundAnnotation bound) $
                "bound type mismatch"
        NamedType ann name ->
          case Map.lookup name (lc ^. #unValidContext) of
            Just (Data a) ->
              \case
                Nothing -> fmap (To' name) <$> getUniversalQuantifierValues a Nothing
                Just (ToBound ann' name' bound) ->
                  if name == name'
                    then fmap (To' name) <$> getUniversalQuantifierValues a (Just bound)
                    else Left . ErrorMessage ann' $ "bound type name mismatch"
                Just bound ->
                  Left . ErrorMessage (boundAnnotation bound) $
                    "bound type mismatch"
            _ -> const . Left . ErrorMessage ann $ "expected the name of a type"
        Maybe _ a ->
          \case
            Nothing ->
              (Maybe'' Nothing :) . fmap (Maybe'' . Just)
                <$> getUniversalQuantifierValues a Nothing
            Just (MaybeBound _ (ValuesBound bound)) ->
              (Maybe'' Nothing :) . fmap (Maybe'' . Just)
                <$> getUniversalQuantifierValues a (Just bound)
            Just bound ->
              Left . ErrorMessage (boundAnnotation bound) $
                "bound type mismatch"
        List ann _ _ ->
          const . Left . ErrorMessage ann $
            "unsupported: universal quantification over lists"
        Map ann _ _ _ ->
          const . Left . ErrorMessage ann $
            "unsupported: universal quantification over maps"

    integerToScalarUnsafe :: Integer -> Scalar
    integerToScalarUnsafe y =
      case integerToScalar y of
        Just y' -> y'
        Nothing -> die "evaluate: integerToScalarUnsafe: integer out of range of scalar (this is a compiler bug)"

    liftLogic ::
      ann ->
      (Bool -> Bool -> Bool) ->
      Value ->
      Value ->
      Either (ErrorMessage ann) Value
    liftLogic ann f =
      curry $
        \case
          (Bool y, Bool z) -> pure (Bool (f y z))
          _ ->
            Left . ErrorMessage ann $
              "expected boolean values"

    mapElems :: ann -> Value -> Either (ErrorMessage ann) [Value]
    mapElems ann =
      \case
        Map'' m -> pure (Map.elems m)
        _ ->
          Left . ErrorMessage ann $
            "expected a map"

    mapFunctor :: (ann -> Value -> Either (ErrorMessage ann) Value) -> ann -> Value -> Either (ErrorMessage ann) Value
    mapFunctor f ann y =
      case y of
        Map'' m -> Map'' <$> mapM (f ann) m
        _ ->
          Left . ErrorMessage ann $
            "Map functor: expected a map"

    mapLookup :: ann -> Value -> Value -> Either (ErrorMessage ann) Value
    mapLookup ann k m =
      case m of
        Map'' m' ->
          case Map.lookup k m' of
            Just v -> pure v
            Nothing ->
              Left . ErrorMessage ann $
                "lookup: key does not exist"
        _ ->
          Left . ErrorMessage ann $
            "lookup: expected a map"

    listSum :: ann -> Value -> Either (ErrorMessage ann) Value
    listSum ann =
      \case
        List'' ys ->
          castF ann . foldl' (Group.+) zero
            =<< mapM (decodeScalar ann) ys
        _ -> Left . ErrorMessage ann $ "expected a list"
    listLength :: ann -> Value -> Either (ErrorMessage ann) Value
    listLength ann =
      \case
        List'' ys ->
          case integerToScalar (intToInteger (length ys)) of
            Just l -> pure (Nat l)
            Nothing ->
              Left . ErrorMessage ann $
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
        _ ->
          Left . ErrorMessage ann $
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
      ann ->
      Value ->
      Either (ErrorMessage ann) Value
    maybeFunctor f ann =
      \case
        Maybe'' (Just y) -> f ann y
        Maybe'' Nothing -> pure (Maybe'' Nothing)
        _ -> Left . ErrorMessage ann $ "Maybe functor: expected a Maybe value"

    listFunctor ::
      (ann -> Value -> Either (ErrorMessage ann) Value) ->
      ann ->
      Value ->
      Either (ErrorMessage ann) Value
    listFunctor f ann =
      \case
        List'' xs -> List'' <$> mapM (f ann) xs
        _ ->
          Left . ErrorMessage ann $
            "List functor: expected a list"

    applyFunWithDefault :: ann -> Value -> PreValue ann -> Value -> Either (ErrorMessage ann) Value
    applyFunWithDefault ann f (Value y) d =
      case f of
        Fun f' ->
          case Map.lookup y f' of
            Just y' -> pure y'
            Nothing -> pure d
        _ -> Left . ErrorMessage ann $ "expected a function"
    applyFunWithDefault ann f y d = flip (applyFunWithDefault ann f) d . Value =<< preValueToValue ann y

    applyFun :: ann -> Value -> PreValue ann -> Either (ErrorMessage ann) Value
    applyFun ann f (Value y) =
      case f of
        Fun f' ->
          case Map.lookup y f' of
            Just y' -> pure y'
            Nothing ->
              Left . ErrorMessage ann $
                "input outside of function domain: " <> pack (show (y, f'))
        _ -> Left . ErrorMessage ann $ "expected a function"
    applyFun ann f y = applyFun ann f . Value =<< preValueToValue ann y

    applyF :: ann -> PreValue ann -> PreValue ann -> Either (ErrorMessage ann) (PreValue ann)
    applyF _ann (LambdaClosure f) y = f y
    applyF ann (Value (Fun f)) y = Value <$> applyFun ann (Fun f) y
    applyF ann _ _ = Left . ErrorMessage ann $ "expected a function"

    partialApplication label ann =
      Left . ErrorMessage ann $
        "encountered a partial function application: " <> pack label

    expectedFunction ann =
      Left . ErrorMessage ann $
        "expected a function in function application head"

evalName ::
  Show ann =>
  ValidContext 'Global ann ->
  ValidContext 'Local ann ->
  EvaluationContext ann ->
  ann ->
  Name ->
  Witness ->
  Either (ErrorMessage ann) (PreValue ann)
evalName gc lc e ann name w =
  case Map.lookup name (e ^. #unEvaluationContext) of
    Just v -> pure v
    Nothing ->
      case Map.lookup name (lc ^. #unValidContext) of
        Just (Defined u y) -> evaluate' gc gcAsLc u y w mempty
        Just (FreeVariable _) ->
          Left . ErrorMessage ann $
            "undefined free variable"
        Just (Data _) ->
          Left . ErrorMessage ann $
            "expected a term denoting a value"
        Nothing ->
          Left . ErrorMessage ann $
            "undefined name: " <> pack (show name)
  where
    gcAsLc = ValidContext (gc ^. #unValidContext)

liftMath :: ann -> (Scalar -> Scalar -> a) -> Value -> Value -> Either (ErrorMessage ann) a
liftMath ann f x y =
  f <$> decodeScalar ann x <*> decodeScalar ann y

decodeScalar :: ann -> Value -> Either (ErrorMessage ann) Scalar
decodeScalar ann =
  \case
    Nat v -> pure v
    Int v -> pure v
    Fin' v -> pure v
    Fp' v -> pure v
    To' _ v -> decodeScalar ann v
    _ -> Left . ErrorMessage ann $ "expected a scalar value"

decodeBool :: ann -> Value -> Either (ErrorMessage ann) Bool
decodeBool ann =
  \case
    Bool v -> pure v
    _ -> Left . ErrorMessage ann $ "expected a boolean value"
