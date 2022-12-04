{-# LANGUAGE LambdaCase #-}

module OSL.Term (termAnnotation) where

import OSL.Types.OSL (Term (..))

termAnnotation :: Term ann -> ann
termAnnotation =
  \case
    NamedTerm ann _ -> ann
    AddN ann -> ann
    MulN ann -> ann
    ConstN ann _ -> ann
    ConstFp ann _ -> ann
    AddFp ann -> ann
    MulFp ann -> ann
    ConstF ann _ -> ann
    ConstSet ann _ -> ann
    AddZ ann -> ann
    MulZ ann -> ann
    ConstZ ann _ -> ann
    MaxN ann -> ann
    MaxZ ann -> ann
    MaxFp ann -> ann
    Cast ann -> ann
    ConstFin ann _ -> ann
    Inverse ann -> ann
    Pair ann -> ann
    Pi1 ann -> ann
    Pi2 ann -> ann
    Iota1 ann -> ann
    Iota2 ann -> ann
    FunctionProduct ann _ _ -> ann
    FunctionCoproduct ann _ _ -> ann
    Lambda ann _ _ _ -> ann
    Apply ann _ _ -> ann
    To ann _ -> ann
    From ann _ -> ann
    Let ann _ _ _ _ -> ann
    Just' ann -> ann
    IsNothing ann -> ann
    Nothing' ann -> ann
    Maybe' ann _ -> ann
    Exists ann -> ann
    MaybePi1 ann -> ann
    MaybePi2 ann -> ann
    MaybeTo ann _ -> ann
    MaybeFrom ann _ -> ann
    Length ann -> ann
    Nth ann -> ann
    ListCast ann -> ann
    ListPi1 ann -> ann
    ListPi2 ann -> ann
    ListTo ann _ -> ann
    ListFrom ann _ -> ann
    ListLength ann -> ann
    ListMaybePi1 ann -> ann
    ListMaybePi2 ann -> ann
    ListMaybeLength ann -> ann
    ListMaybeTo ann _ -> ann
    ListMaybeFrom ann _ -> ann
    Sum ann -> ann
    Lookup ann -> ann
    Keys ann -> ann
    MapPi1 ann -> ann
    MapPi2 ann -> ann
    MapTo ann _ -> ann
    MapFrom ann _ -> ann
    SumMapLength ann -> ann
    SumListLookup ann _ -> ann
    Equal ann _ _ -> ann
    LessOrEqual ann _ _ -> ann
    And ann _ _ -> ann
    Or ann _ _ -> ann
    Not ann _ -> ann
    Implies ann _ _ -> ann
    Iff ann _ _ -> ann
    ForAll ann _ _ _ _ -> ann
    ForSome ann _ _ _ _ -> ann
    Top ann -> ann
    Bottom ann -> ann
