{-# LANGUAGE LambdaCase #-}

module OSL.Term
  ( applicationHead,
    lambdaBody,
    termAnnotation,
    dropTermAnnotations,
  )
where

import Control.Arrow ((***))
import OSL.Type (dropTypeAnnotations)
import OSL.Types.OSL (Bound (..), CodomainBound (..), DomainBound (..), KeysBound (..), LeftBound (..), RightBound (..), Term (..), ValuesBound (..))

applicationHead :: Term ann -> Term ann
applicationHead (Apply _ f _) = applicationHead f
applicationHead f = f

lambdaBody :: Term ann -> Term ann
lambdaBody (Lambda _ _ _ body) = lambdaBody body
lambdaBody body = body

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

dropTermAnnotations :: Term ann -> Term ()
dropTermAnnotations =
  \case
    NamedTerm _ name -> NamedTerm () name
    AddN _ -> AddN ()
    MulN _ -> MulN ()
    ConstN _ i -> ConstN () i
    ConstFp _ i -> ConstFp () i
    AddFp _ -> AddFp ()
    MulFp _ -> MulFp ()
    ConstF _ f -> ConstF () ((rec *** rec) <$> f)
    ConstSet _ s -> ConstSet () (rec <$> s)
    AddZ _ -> AddZ ()
    MulZ _ -> MulZ ()
    ConstZ _ i -> ConstZ () i
    MaxN _ -> MaxN ()
    MaxZ _ -> MaxZ ()
    Cast _ -> Cast ()
    ConstFin _ i -> ConstFin () i
    Inverse _ -> Inverse ()
    Pair _ -> Pair ()
    Pi1 _ -> Pi1 ()
    Pi2 _ -> Pi2 ()
    Iota1 _ -> Iota1 ()
    Iota2 _ -> Iota2 ()
    FunctionProduct _ f g ->
      FunctionProduct () (rec f) (rec g)
    FunctionCoproduct _ f g ->
      FunctionCoproduct () (rec f) (rec g)
    Lambda _ v a y ->
      Lambda () v (recType a) (rec y)
    Apply _ f g ->
      Apply () (rec f) (rec g)
    To _ name -> To () name
    From _ name -> From () name
    Let _ v a d y ->
      Let () v (recType a) (rec d) (rec y)
    IsNothing _ -> IsNothing ()
    Just' _ -> Just' ()
    Nothing' _ -> Nothing' ()
    Maybe' _ f -> Maybe' () (rec f)
    MaybePi1 _ -> MaybePi1 ()
    MaybePi2 _ -> MaybePi2 ()
    MaybeTo _ name -> MaybeTo () name
    MaybeFrom _ name -> MaybeFrom () name
    MaxFp _ -> MaxFp ()
    Exists _ -> Exists ()
    Length _ -> Length ()
    Nth _ -> Nth ()
    ListCast _ -> ListCast ()
    ListPi1 _ -> ListPi1 ()
    ListPi2 _ -> ListPi2 ()
    ListTo _ name -> ListTo () name
    ListFrom _ name -> ListFrom () name
    ListLength _ -> ListLength ()
    ListMaybePi1 _ -> ListMaybePi1 ()
    ListMaybePi2 _ -> ListMaybePi2 ()
    ListMaybeLength _ -> ListMaybeLength ()
    ListMaybeFrom _ name -> ListMaybeFrom () name
    ListMaybeTo _ name -> ListMaybeTo () name
    Sum _ -> Sum ()
    Lookup _ -> Lookup ()
    Keys _ -> Keys ()
    MapPi1 _ -> MapPi1 ()
    MapPi2 _ -> MapPi2 ()
    MapTo _ name -> MapTo () name
    MapFrom _ name -> MapFrom () name
    SumMapLength _ -> SumMapLength ()
    SumListLookup _ k -> SumListLookup () (rec k)
    Equal _ x y -> Equal () (rec x) (rec y)
    LessOrEqual _ x y -> LessOrEqual () (rec x) (rec y)
    And _ p q -> And () (rec p) (rec q)
    Or _ p q -> Or () (rec p) (rec q)
    Not _ p -> Not () (rec p)
    Implies _ p q -> Implies () (rec p) (rec q)
    Iff _ p q -> Iff () (rec p) (rec q)
    ForAll _ x a b p -> ForAll () x (recType a) (recBound <$> b) (rec p)
    ForSome _ x a b p -> ForSome () x (recType a) (recBound <$> b) (rec p)
    Top _ -> Top ()
    Bottom _ -> Bottom ()
  where
    rec = dropTermAnnotations
    recType = dropTypeAnnotations
    recBound = dropBoundAnnotations

dropBoundAnnotations :: Bound ann -> Bound ()
dropBoundAnnotations =
  \case
    ScalarBound _ b -> ScalarBound () (dropTermAnnotations b)
    FieldMaxBound _ -> FieldMaxBound ()
    ProductBound _ (LeftBound a) (RightBound b) ->
      ProductBound () (LeftBound (rec a)) (RightBound (rec b))
    CoproductBound _ (LeftBound a) (RightBound b) ->
      CoproductBound () (LeftBound (rec a)) (RightBound (rec b))
    FunctionBound _ (DomainBound a) (CodomainBound b) ->
      FunctionBound () (DomainBound (rec a)) (CodomainBound (rec b))
    ListBound _ (ValuesBound a) -> ListBound () (ValuesBound (rec a))
    MaybeBound _ (ValuesBound a) -> MaybeBound () (ValuesBound (rec a))
    MapBound _ (KeysBound a) (ValuesBound b) ->
      MapBound () (KeysBound (rec a)) (ValuesBound (rec b))
    ToBound _ name a -> ToBound () name (rec a)
  where
    rec = dropBoundAnnotations
