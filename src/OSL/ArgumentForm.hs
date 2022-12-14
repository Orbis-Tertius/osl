{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.ArgumentForm (getArgumentForm) where

import Control.Lens ((^.))
import Data.Map (Map)
import qualified Data.Map as Map
import OSL.Type (dropTypeAnnotations)
import OSL.Types.ArgumentForm (ArgumentForm (ArgumentForm), StatementType (StatementType), WitnessType (WitnessType))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.OSL (ContextType (Global, Local), Declaration (Defined, FreeVariable), Name, Term (AddFp, AddN, AddZ, And, Apply, Bottom, Cast, ConstF, ConstFin, ConstFp, ConstN, ConstSet, ConstZ, Equal, Exists, ForAll, ForSome, From, FunctionCoproduct, FunctionProduct, Iff, Implies, Inverse, Iota1, Iota2, IsNothing, Just', Keys, Lambda, Length, LessOrEqual, Let, ListCast, ListFrom, ListLength, ListMaybeFrom, ListMaybeLength, ListMaybePi1, ListMaybePi2, ListMaybeTo, ListPi1, ListPi2, ListTo, Lookup, MapFrom, MapPi1, MapPi2, MapTo, MaxFp, MaxN, MaxZ, Maybe', MaybeFrom, MaybePi1, MaybePi2, MaybeTo, MulFp, MulN, MulZ, NamedTerm, Not, Nothing', Nth, Or, Pair, Pi1, Pi2, Sum, SumListLookup, SumMapLength, To, Top), Type (Coproduct, F, Fin, Fp, List, Map, Maybe, N, NamedType, P, Product, Prop, Z), ValidContext (ValidContext))

getArgumentForm :: ValidContext 'Global ann -> Type ann -> Term ann -> Either (ErrorMessage ann) ArgumentForm
getArgumentForm gc t x =
  ArgumentForm <$> getStatementType gc t <*> getWitnessType gc lc (ContextBacklinks mempty) x
  where
    lc = ValidContext (gc ^. #unValidContext)

getStatementType :: ValidContext 'Global ann -> Type ann -> Either (ErrorMessage ann) StatementType
getStatementType c =
  \case
    Prop _ -> pure unit
    F _ _ a b -> do
      prod (StatementType (dropTypeAnnotations a))
        <$> getStatementType c b
    P ann _ _ _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a permutation"
    N ann ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be an N"
    Z ann ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a Z"
    Fp ann ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be an Fp"
    Fin ann _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a Fin"
    Product ann _ _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a Product"
    Coproduct ann _ _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a Coproduct"
    NamedType ann _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a named type"
    Maybe ann _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a Maybe"
    List ann _ _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a List"
    Map ann _ _ _ ->
      Left . ErrorMessage ann $
        "getArgumentForm: an argument cannot be a Map"
  where
    unit :: StatementType
    unit = StatementType (Fin () 1)

    prod :: StatementType -> StatementType -> StatementType
    prod (StatementType a) (StatementType b) =
      StatementType (Product () a b)

newtype ContextBacklinks ann = ContextBacklinks
  { unContextBacklinks ::
      Map Name (ValidContext 'Local ann, ContextBacklinks ann)
  }

getWitnessType ::
  ValidContext 'Global ann ->
  ValidContext 'Local ann ->
  ContextBacklinks ann ->
  Term ann ->
  Either (ErrorMessage ann) WitnessType
getWitnessType gc lc lcs =
  \case
    Top _ -> pure empty
    Bottom _ -> pure empty
    ForAll _ v a _ p -> do
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      WitnessType pT <- rec lc' lcs p
      pure (WitnessType (F () Nothing (dropTypeAnnotations a) pT))
    ForSome _ v a _ p -> do
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      prod (WitnessType (dropTypeAnnotations a)) <$> rec lc' lcs p
    Let _ v a def body -> do
      let lc' = lc <> ValidContext (Map.singleton v (Defined a def))
          lcs' = ContextBacklinks (Map.insert v (lc, lcs) (unContextBacklinks lcs))
      prod <$> rec lc lcs def <*> rec lc' lcs' body
    Lambda _ v a body -> do
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
          lcs' = ContextBacklinks (Map.insert v (lc, lcs) (unContextBacklinks lcs))
      rec lc' lcs' body
    NamedTerm ann name ->
      case Map.lookup name (lc ^. #unValidContext) of
        Just (Defined _ def) ->
          case Map.lookup name (unContextBacklinks lcs) of
            Just (lc', lcs') ->
              rec lc' lcs' def
            Nothing ->
              rec gcAsLc (ContextBacklinks mempty) def
        _ -> Left . ErrorMessage ann $ "undefined term"
    Apply _ f _ -> rec lc lcs f
    Iff _ p q -> prod <$> rec lc lcs p <*> rec lc lcs q
    Implies _ p q -> prod <$> rec lc lcs p <*> rec lc lcs q
    Not _ p -> rec lc lcs p
    Or _ p q -> prod <$> rec lc lcs p <*> rec lc lcs q
    And _ p q -> prod <$> rec lc lcs p <*> rec lc lcs q
    LessOrEqual {} -> pure empty
    Equal {} -> pure empty
    SumListLookup {} -> pure empty
    SumMapLength {} -> pure empty
    MapFrom {} -> pure empty
    MapTo {} -> pure empty
    MapPi2 {} -> pure empty
    MapPi1 {} -> pure empty
    Keys {} -> pure empty
    Lookup {} -> pure empty
    Sum {} -> pure empty
    ListMaybeTo {} -> pure empty
    ListMaybeFrom {} -> pure empty
    ListMaybeLength {} -> pure empty
    ListMaybePi1 {} -> pure empty
    ListMaybePi2 {} -> pure empty
    ListFrom {} -> pure empty
    ListTo {} -> pure empty
    ListPi1 {} -> pure empty
    ListPi2 {} -> pure empty
    ListCast {} -> pure empty
    Nth {} -> pure empty
    Length {} -> pure empty
    Exists {} -> pure empty
    MaxFp {} -> pure empty
    MaxZ {} -> pure empty
    MaxN {} -> pure empty
    MaybeFrom {} -> pure empty
    MaybeTo {} -> pure empty
    MaybePi1 {} -> pure empty
    MaybePi2 {} -> pure empty
    Maybe' {} -> pure empty
    Nothing' {} -> pure empty
    Just' {} -> pure empty
    IsNothing {} -> pure empty
    To {} -> pure empty
    From {} -> pure empty
    FunctionCoproduct {} -> pure empty
    FunctionProduct {} -> pure empty
    Iota1 {} -> pure empty
    Iota2 {} -> pure empty
    Pi1 {} -> pure empty
    Pi2 {} -> pure empty
    Pair {} -> pure empty
    Inverse {} -> pure empty
    ConstSet {} -> pure empty
    ConstF {} -> pure empty
    ConstFin {} -> pure empty
    ConstFp {} -> pure empty
    ConstZ {} -> pure empty
    Cast {} -> pure empty
    AddFp {} -> pure empty
    MulFp {} -> pure empty
    AddZ {} -> pure empty
    MulZ {} -> pure empty
    ConstN {} -> pure empty
    AddN {} -> pure empty
    MulN {} -> pure empty
    ListLength {} -> pure empty
  where
    rec = getWitnessType gc

    empty :: WitnessType
    empty = WitnessType (Fin () 1)

    prod :: WitnessType -> WitnessType -> WitnessType
    prod (WitnessType a) (WitnessType b) =
      WitnessType (Product () a b)

    gcAsLc = ValidContext (gc ^. #unValidContext)
