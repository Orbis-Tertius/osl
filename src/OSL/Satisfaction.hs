{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Satisfaction (satisfies, satisfiesSimple) where

import Control.Lens ((^.))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Tuple.Extra (curry3)
import Die (die)
import OSL.Evaluation (evaluate)
import OSL.Term (termAnnotation)
import OSL.Types.Argument (Argument (Argument), Statement (Statement))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.OSL (ContextType (Global, Local), Declaration (FreeVariable, Defined, Data), Term (Lambda, NamedTerm, AddN, MulN, AddZ, MulZ, AddFp, MulFp, ConstN, ConstZ, ConstFp, ConstFin, ConstF, ConstSet, Cast, Inverse, Pair, Pi1, Pi2, Iota1, Iota2, FunctionProduct, FunctionCoproduct, Apply, To, From, Let, IsNothing, Just', Nothing', Maybe', MaybePi1, MaybePi2, MaybeTo, MaybeFrom, MaxN, MaxZ, MaxFp, Exists, Length, Nth, ListCast, ListPi1, ListPi2, ListTo, ListFrom, ListLength, ListMaybePi1, ListMaybePi2, ListMaybeLength, ListMaybeFrom, ListMaybeTo, Sum, Lookup, Keys, MapPi1, MapPi2, MapTo, MapFrom, SumMapLength, SumListLookup, Equal, LessOrEqual, And, Or, Not, Implies, Iff, ForAll, ForSome, Top, Bottom), Type (F), ValidContext (ValidContext), Bound (FieldMaxBound, ScalarBound, ProductBound, CoproductBound, FunctionBound, ListBound, MaybeBound, MapBound, ToBound), LeftBound (LeftBound), RightBound (RightBound), DomainBound (DomainBound), CodomainBound (CodomainBound), ValuesBound (ValuesBound), KeysBound (KeysBound))
import OSL.Types.PreValue (PreValue (Value))
import OSL.Types.Value (Value (Bool, Pair'))
import OSL.ValidateContext (inferType)
import OSL.Witness (preprocessWitness)

satisfiesSimple :: (Ord ann, Show ann) => ValidContext 'Global ann -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfiesSimple c x arg = do
  xT <- inferType c x
  satisfies c (ValidContext (c ^. #unValidContext)) mempty xT x arg

satisfies :: (Ord ann, Show ann) => ValidContext 'Global ann -> ValidContext 'Local ann -> EvaluationContext ann -> Type ann -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfies gc lc e = curry3 $
  \case
    ( F _ann _n a b,
      Lambda _ann' v _a' body,
      Argument (Statement (Pair' vs s')) w
      ) ->
        satisfies
          gc
          (lc <> ValidContext (Map.singleton v (FreeVariable a)))
          (e <> EvaluationContext (Map.singleton v (Value vs)))
          b
          body
          (Argument (Statement s') w)
    ( F {}, Lambda ann _v _a _body, _ ) ->
      Left . ErrorMessage ann $
        "expected statement to be a pair but it was not"
    ( _, Lambda ann _v _a _Body, _ ) ->
      Left . ErrorMessage ann $
        "expected lambda type to be a function type but it was not"
    (a, NamedTerm ann name, arg) ->
      case Map.lookup name (lc ^. #unValidContext) of
        Just (Defined _ def) -> satisfies gc lc e a def arg
        _ -> Left . ErrorMessage ann $
          "expected the name of a defined predicate"
    (a, x, Argument _ w) -> do
      pw <- preprocessWitness (getAnnotationContext gc) x w
      (== Bool True) <$> evaluate gc pw lc a x e

getAnnotationContext :: Ord ann => ValidContext 'Global ann -> ann -> ValidContext 'Local ann
getAnnotationContext gc =
  \ann ->
    case Map.lookup ann gam of
      Just lc -> lc
      Nothing -> die "getAnnotationContext: failed lookup in global annotation map (this is a compiler bug)"
  where
    gam = getGlobalAnnotationMap gc

getGlobalAnnotationMap :: Ord ann => ValidContext 'Global ann -> Map ann (ValidContext 'Local ann)
getGlobalAnnotationMap gc =
  mconcat
    [ getDeclarationAnnotationMap gc decl
    | decl <- Map.elems (gc ^. #unValidContext)
    ]

getDeclarationAnnotationMap :: Ord ann => ValidContext 'Global ann -> Declaration ann -> Map ann (ValidContext 'Local ann)
getDeclarationAnnotationMap gc =
  \case
    FreeVariable _ -> mempty
    Data _ -> mempty
    Defined _ def -> getTermAnnotationMap gc def

getTermAnnotationMap :: Ord ann => ValidContext 'Global ann -> Term ann -> Map ann (ValidContext 'Local ann)
getTermAnnotationMap gc t =
  Map.singleton (termAnnotation t) lc <>
    getSubtermsAnnotationMap lc t
  where
    lc = ValidContext (gc ^. #unValidContext)

getSubtermsAnnotationMap :: Ord ann => ValidContext 'Local ann -> Term ann -> Map ann (ValidContext 'Local ann)
getSubtermsAnnotationMap lc =
  \case
    NamedTerm {} -> mempty
    AddN _ -> mempty
    MulN _ -> mempty
    AddZ _ -> mempty
    MulZ _ -> mempty
    AddFp _ -> mempty
    MulFp _ -> mempty
    ConstN {} -> mempty
    ConstZ {} -> mempty
    ConstFp {} -> mempty
    ConstFin {} -> mempty
    Cast _ -> mempty
    ConstF _ f ->
      mconcat
        [ rec lc x <> rec lc y
        | (x,y) <- f
        ]
    ConstSet _ s ->
      mconcat $ rec lc <$> s
    Inverse _ -> mempty
    Pair _ -> mempty
    Pi1 _ -> mempty
    Pi2 _ -> mempty
    Iota1 _ -> mempty
    Iota2 _ -> mempty
    FunctionProduct _ f g ->
      rec lc f <> rec lc g
    FunctionCoproduct _ f g ->
      rec lc f <> rec lc g
    Lambda _ v a body ->
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      in rec lc' body
    Apply _ f g ->
      rec lc f <> rec lc g
    From {} -> mempty
    To {} -> mempty
    Let _ v a def body ->
      let lc' = lc <> ValidContext (Map.singleton v (Defined a def))
      in rec lc def <> rec lc' body
    IsNothing _ -> mempty
    Just' _ -> mempty
    Nothing' _ -> mempty
    Maybe' _ x -> rec lc x
    MaybePi1 _ -> mempty
    MaybePi2 _ -> mempty
    MaybeTo {} -> mempty
    MaybeFrom {} -> mempty
    MaxN _ -> mempty
    MaxZ _ -> mempty
    MaxFp _ -> mempty
    Exists _ -> mempty
    Length _ -> mempty
    Nth _ -> mempty
    ListCast _ -> mempty
    ListPi1 _ -> mempty
    ListPi2 _ -> mempty
    ListTo {} -> mempty
    ListFrom {} -> mempty
    ListLength {} -> mempty
    ListMaybePi1 {} -> mempty
    ListMaybePi2 {} -> mempty
    ListMaybeLength {} -> mempty
    ListMaybeFrom {} -> mempty
    ListMaybeTo {} -> mempty
    Sum {} -> mempty
    Lookup {} -> mempty
    Keys _ -> mempty
    MapPi1 _ -> mempty
    MapPi2 _ -> mempty
    MapTo {} -> mempty
    MapFrom {} -> mempty
    SumMapLength _ -> mempty
    SumListLookup _ x -> rec lc x
    Equal _ x y -> rec lc x <> rec lc y
    LessOrEqual _ x y -> rec lc x <> rec lc y
    And _ p q -> rec lc p <> rec lc q
    Or _ p q -> rec lc p <> rec lc q
    Not _ p -> rec lc p
    Implies _ p q -> rec lc p <> rec lc q
    Iff _ p q -> rec lc p <> rec lc q
    ForAll _ v a bound p ->
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      in rec lc' p <> maybe mempty (getBoundAnnotationMap lc) bound
    ForSome _ v a bound p ->
      let lc' = lc <> ValidContext (Map.singleton v (FreeVariable a))
      in rec lc' p <> maybe mempty (getBoundAnnotationMap lc) bound
    Bottom _ -> mempty
    Top _ -> mempty
  where
    rec lc' x =
      Map.singleton (termAnnotation x) lc' <> getSubtermsAnnotationMap lc' x

getBoundAnnotationMap :: Ord ann => ValidContext 'Local ann -> Bound ann -> Map ann (ValidContext 'Local ann)
getBoundAnnotationMap lc =
  \case
    FieldMaxBound ann -> Map.singleton ann lc
    ScalarBound ann x ->
      Map.singleton ann lc <> Map.singleton (termAnnotation x) lc
        <> getSubtermsAnnotationMap lc x
    ProductBound ann (LeftBound a) (RightBound b) ->
      Map.singleton ann lc <> rec a <> rec b
    CoproductBound ann (LeftBound a) (RightBound b) ->
      Map.singleton ann lc <> rec a <> rec b
    FunctionBound ann (DomainBound a) (CodomainBound b) ->
      Map.singleton ann lc <> rec a <> rec b
    ListBound ann (ValuesBound a) ->
      Map.singleton ann lc <> rec a
    MaybeBound ann (ValuesBound a) ->
      Map.singleton ann lc <> rec a
    MapBound ann (KeysBound a) (ValuesBound b) ->
      Map.singleton ann lc <> rec a <> rec b
    ToBound ann _ a ->
      Map.singleton ann lc <> rec a
  where
    rec = getBoundAnnotationMap lc
