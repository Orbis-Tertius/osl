{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.ArgumentForm (getArgumentForm) where

import Control.Lens ((^.))
import qualified Data.Map as Map
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
      (StatementType (dropTypeAnnotations a) <>) <$> getStatementType c b
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

-- TODO: must carry local context around to correctly handle
-- Prop-valued lambdas in let expressions.
getWitnessType :: ValidContext 'Global ann -> Term ann -> Either (ErrorMessage ann) WitnessType
getWitnessType c =
  \case
    Top _ -> pure mempty
    Bottom _ -> pure mempty
    ForAll _ _ a _ p -> do
      WitnessType pT <- rec p
      pure (WitnessType (F () Nothing (dropTypeAnnotations a) pT))
    ForSome _ _ a _ p ->
      (WitnessType (dropTypeAnnotations a) <>) <$> rec p
    Let _ _ _ _ body -> rec body
    Lambda _ _ _ body -> rec body
    Apply _ (NamedTerm ann f) _ -> do
      case Map.lookup f (c ^. #unValidContext) of
        Just (Defined _ def) -> rec def
        _ -> Left . ErrorMessage ann $ "expected the name of a defined predicate"
    Apply _ (Lambda _ _ _ body) _ -> rec body
    Apply _ (Let _ _ _ _ body) _ -> rec body
    Apply {} -> pure mempty
    Iff _ p q -> rec p <> rec q
    Implies _ p q -> rec p <> rec q
    Not _ p -> rec p
    Or _ p q -> rec p <> rec q
    And _ p q -> rec p <> rec q
    LessOrEqual {} -> pure mempty
    Equal {} -> pure mempty
    SumListLookup {} -> pure mempty
    SumMapLength {} -> pure mempty
    MapFrom {} -> pure mempty
    MapTo {} -> pure mempty
    MapPi2 {} -> pure mempty
    MapPi1 {} -> pure mempty
    Keys {} -> pure mempty
    Lookup {} -> pure mempty
    Sum {} -> pure mempty
    ListMaybeTo {} -> pure mempty
    ListMaybeFrom {} -> pure mempty
    ListMaybeLength {} -> pure mempty
    ListMaybePi1 {} -> pure mempty
    ListMaybePi2 {} -> pure mempty
    ListFrom {} -> pure mempty
    ListTo {} -> pure mempty
    ListPi1 {} -> pure mempty
    ListPi2 {} -> pure mempty
    ListCast {} -> pure mempty
    Nth {} -> pure mempty
    Length {} -> pure mempty
    Exists {} -> pure mempty
    MaxFp {} -> pure mempty
    MaxZ {} -> pure mempty
    MaxN {} -> pure mempty
    MaybeFrom {} -> pure mempty
    MaybeTo {} -> pure mempty
    MaybePi1 {} -> pure mempty
    MaybePi2 {} -> pure mempty
    Maybe' {} -> pure mempty
    Nothing' {} -> pure mempty
    Just' {} -> pure mempty
    IsNothing {} -> pure mempty
    To {} -> pure mempty
    From {} -> pure mempty
    FunctionCoproduct {} -> pure mempty
    FunctionProduct {} -> pure mempty
    Iota1 {} -> pure mempty
    Iota2 {} -> pure mempty
    Pi1 {} -> pure mempty
    Pi2 {} -> pure mempty
    Pair {} -> pure mempty
    Inverse {} -> pure mempty
    ConstSet {} -> pure mempty
    ConstF {} -> pure mempty
    ConstFin {} -> pure mempty
    ConstFp {} -> pure mempty
    ConstZ {} -> pure mempty
    Cast {} -> pure mempty
    AddFp {} -> pure mempty
    MulFp {} -> pure mempty
    AddZ {} -> pure mempty
    MulZ {} -> pure mempty
    ConstN {} -> pure mempty
    AddN {} -> pure mempty
    MulN {} -> pure mempty
    NamedTerm {} -> pure mempty
    ListLength {} -> pure mempty
  where
    rec = getWitnessType c

dropTypeAnnotations :: Type ann -> Type ()
dropTypeAnnotations =
  \case
    Prop _ -> Prop ()
    F _ n a b -> F () n (rec a) (rec b)
    P _ n a b -> P () n (rec a) (rec b)
    N _ -> N ()
    Z _ -> Z ()
    Fp _ -> Fp ()
    Fin _ i -> Fin () i
    Product _ a b -> Product () (rec a) (rec b)
    Coproduct _ a b -> Coproduct () (rec a) (rec b)
    NamedType _ name -> NamedType () name
    Maybe _ a -> Maybe () (rec a)
    List _ n a -> List () n (rec a)
    Map _ n a b -> Map () n (rec a) (rec b)
  where
    rec = dropTypeAnnotations
