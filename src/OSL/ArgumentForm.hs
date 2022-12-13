{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.ArgumentForm (getArgumentForm) where

import Control.Lens ((^.))
import qualified Data.Map as Map
import OSL.Type (dropTypeAnnotations)
import OSL.Types.ArgumentForm (ArgumentForm (ArgumentForm), StatementType (StatementType), WitnessType (WitnessType))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.OSL (ContextType (Global), Declaration (Defined), Term (AddFp, AddN, AddZ, And, Apply, Bottom, Cast, ConstF, ConstFin, ConstFp, ConstN, ConstSet, ConstZ, Equal, Exists, ForAll, ForSome, From, FunctionCoproduct, FunctionProduct, Iff, Implies, Inverse, Iota1, Iota2, IsNothing, Just', Keys, Lambda, Length, LessOrEqual, Let, ListCast, ListFrom, ListLength, ListMaybeFrom, ListMaybeLength, ListMaybePi1, ListMaybePi2, ListMaybeTo, ListPi1, ListPi2, ListTo, Lookup, MapFrom, MapPi1, MapPi2, MapTo, MaxFp, MaxN, MaxZ, Maybe', MaybeFrom, MaybePi1, MaybePi2, MaybeTo, MulFp, MulN, MulZ, NamedTerm, Not, Nothing', Nth, Or, Pair, Pi1, Pi2, Sum, SumListLookup, SumMapLength, To, Top), Type (Coproduct, F, Fin, Fp, List, Map, Maybe, N, NamedType, P, Product, Prop, Z), ValidContext)

getArgumentForm :: ValidContext 'Global ann -> Type ann -> Term ann -> Either (ErrorMessage ann) ArgumentForm
getArgumentForm c t x =
  ArgumentForm <$> getStatementType c t <*> getWitnessType c x

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

-- TODO: must carry local context around to correctly handle
-- Prop-valued lambdas in let expressions.
getWitnessType :: ValidContext 'Global ann -> Term ann -> Either (ErrorMessage ann) WitnessType
getWitnessType c =
  \case
    Top _ -> pure empty
    Bottom _ -> pure empty
    ForAll _ _ a _ p -> do
      WitnessType pT <- rec p
      pure (WitnessType (F () Nothing (dropTypeAnnotations a) pT))
    ForSome _ _ a _ p ->
      prod (WitnessType (dropTypeAnnotations a)) <$> rec p
    Let _ _ _ _ body -> rec body
    Lambda _ _ _ body -> rec body
    NamedTerm ann name ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (Defined _ def) -> rec def
        _ -> Left . ErrorMessage ann $ "undefined term"
    Apply _ f _ -> rec f
    Iff _ p q -> prod <$> rec p <*> rec q
    Implies _ p q -> prod <$> rec p <*> rec q
    Not _ p -> rec p
    Or _ p q -> prod <$> rec p <*> rec q
    And _ p q -> prod <$> rec p <*> rec q
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
    rec = getWitnessType c

    empty :: WitnessType
    empty = WitnessType (Fin () 1)

    prod :: WitnessType -> WitnessType -> WitnessType
    prod (WitnessType a) (WitnessType b) =
      WitnessType (Product () a b)
