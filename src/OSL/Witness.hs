{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Witness (preprocessWitness) where

import Control.Lens ((^.), _1)
import Control.Monad (when)
import Control.Monad.Trans.Class (MonadTrans (lift))
import Control.Monad.Trans.State (State, evalState, evalStateT, get, put)
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (pack)
import Die (die)
import OSL.Term (termAnnotation)
import OSL.Types.Argument (Witness (Witness))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.EvaluationContext (EvaluationContext)
import OSL.Types.OSL (Term (AddFp, AddN, AddZ, And, Apply, Bottom, Cast, ConstF, ConstFin, ConstFp, ConstN, ConstSet, ConstZ, Equal, Exists, ForAll, ForSome, From, FunctionCoproduct, FunctionProduct, Iff, Implies, Inverse, Iota1, Iota2, IsNothing, Just', Keys, Lambda, Length, LessOrEqual, Let, ListCast, ListFrom, ListLength, ListMaybeFrom, ListMaybeLength, ListMaybePi1, ListMaybePi2, ListMaybeTo, ListPi1, ListPi2, ListTo, Lookup, MapFrom, MapPi1, MapPi2, MapTo, MaxFp, MaxN, MaxZ, Maybe', MaybeFrom, MaybePi1, MaybePi2, MaybeTo, MulFp, MulN, MulZ, NamedTerm, Not, Nothing', Nth, Or, Pair, Pi1, Pi2, Sum, SumListLookup, SumMapLength, To, Top), ValidContext, ContextType (Local), Declaration (Defined, FreeVariable))
import OSL.Types.PreprocessedWitness (PreprocessedWitness (PreprocessedWitness))
import OSL.Types.PreValue (PreValue (Value))
import OSL.Types.Value (Value (Fun, Pair'))

preprocessWitness ::
  (Ord ann, Show ann) =>
  (ann -> ValidContext 'Local ann) ->
  Term ann ->
  Witness ->
  Either (ErrorMessage ann) (PreprocessedWitness ann)
preprocessWitness lc x0 w0 =
  pure $ PreprocessedWitness (\ann e -> go x0 w0 ann e `evalStateT` mempty)
  where
    go x (Witness w) ann e = do
      let xAnn = termAnnotation x
      visited <- get
      when (xAnn `Set.member` visited) . lift . Left . ErrorMessage ann
        $ "preprocessWitness: go: infinite loop detected: " <> pack (show ann)
      put (visited <> Set.singleton xAnn)
      if xAnn == ann
        then case x of
          ForSome {} ->
            (^. #unWitness) . fst <$> lift (splitWitness ann (Witness w))
          _ ->
            lift . Left . ErrorMessage ann $
              "tried to apply preprocessed witness to the annotation of a term which is not an existential quantifier (this is a compiler bug)"
        else -- traverse term and witness
        case Map.lookup ann telescopes of
          Nothing -> lift . Left . ErrorMessage ann $ "telescope not found (this is a compiler bug)"
          Just (Telescope []) ->
            lift . Left . ErrorMessage ann $ "empty telescope (this is a compiler bug)"
          Just (Telescope [_]) ->
            lift . Left . ErrorMessage ann $ "premature end of telescope (this is a compiler bug)"
          Just (Telescope (t0 : t1 : _)) ->
            if t0 == x
              then do
                branches <- lift $ getDirectSubformulasAndPairedWitnesses lc x (Witness w) e
                case find ((== termAnnotation t1) . termAnnotation . (^. _1)) branches of
                  Just (u, v, e') -> go u v ann e'
                  Nothing ->
                    lift . Left . ErrorMessage ann $
                      "telescope traversal failed (this is a compiler bug)"
              else pure w
    telescopes = getSubformulaTelescopes lc x0 `evalState` mempty

-- The telescope of a subterm is the sequence of its enclosing subterms, beginning with
-- the overall term and ending with the subterm itself. Having the telescope
-- of a subterm helps with traversing the overall formula and concurrently traversing
-- the witness in order to find the piece of the witness that is relevant to the
-- given annotation and the evaluation context.
newtype Telescope ann = Telescope [Term ann]
  deriving newtype (Eq, Ord, Show, Semigroup, Monoid)

-- Get the map of subformula annotations to their telescopes.
-- In order to terminate, it carries a set of annotations that have
-- been visited.
getSubformulaTelescopes ::
  Ord ann =>
  (ann -> ValidContext 'Local ann) ->
  Term ann ->
  State (Set ann) (Map ann (Telescope ann))
getSubformulaTelescopes lc x = do
  visited <- get
  put (Set.singleton (termAnnotation x) <> visited)
  let newSubformulas = filter (not . (`Set.member` visited) . termAnnotation) $
        getDirectSubformulas lc x
      t = Telescope [x]
  ts <- mconcat <$> mapM (getSubformulaTelescopes lc) newSubformulas
  pure $ ((t <>) <$> ts) <> Map.singleton (termAnnotation x) t

getDirectSubformulas :: (ann -> ValidContext 'Local ann) -> Term ann -> [Term ann]
getDirectSubformulas lc =
  \case
    NamedTerm ann name ->
      case Map.lookup name (lc ann ^. #unValidContext) of
        Just (Defined _ def) -> [def]
        Just (FreeVariable _) -> mempty
        _ -> die "getDirectSubformulas: expected the name of a term (this is a compiler bug)"
    AddN _ -> mempty
    AddFp _ -> mempty
    AddZ _ -> mempty
    And _ p q -> [p, q]
    Apply _ f _ -> [f]
    Bottom _ -> mempty
    Cast _ -> mempty
    ConstF {} -> mempty
    ConstFin {} -> mempty
    ConstFp {} -> mempty
    ConstN {} -> mempty
    ConstSet {} -> mempty
    ConstZ {} -> mempty
    Equal {} -> mempty
    Exists _ -> mempty
    ForAll _ _ _ _ p -> [p]
    ForSome _ _ _ _ p -> [p]
    From {} -> mempty
    FunctionCoproduct {} -> mempty
    FunctionProduct {} -> mempty
    Iff _ p q -> [p, q]
    Implies _ p q -> [p, q]
    Inverse _ -> mempty
    Iota1 _ -> mempty
    Iota2 _ -> mempty
    IsNothing _ -> mempty
    Just' _ -> mempty
    Keys _ -> mempty
    Lambda _ _ _ p -> [p]
    Length _ -> mempty
    LessOrEqual {} -> mempty
    Let _ann _v _a _def body -> [body]
    ListCast _ -> mempty
    ListFrom {} -> mempty
    ListLength _ -> mempty
    ListMaybeFrom {} -> mempty
    ListMaybeLength _ -> mempty
    ListMaybePi1 _ -> mempty
    ListMaybePi2 _ -> mempty
    ListMaybeTo {} -> mempty
    ListPi1 _ -> mempty
    ListPi2 _ -> mempty
    ListTo {} -> mempty
    Lookup {} -> mempty
    MapFrom {} -> mempty
    MapPi1 _ -> mempty
    MapPi2 _ -> mempty
    MapTo {} -> mempty
    MaxFp _ -> mempty
    MaxN _ -> mempty
    MaxZ _ -> mempty
    Maybe' {} -> mempty
    MaybeFrom {} -> mempty
    MaybePi1 _ -> mempty
    MaybePi2 _ -> mempty
    MaybeTo {} -> mempty
    MulFp _ -> mempty
    MulN _ -> mempty
    MulZ _ -> mempty
    Not _ p -> [p]
    Nothing' _ -> mempty
    Nth _ -> mempty
    Or _ p q -> [p, q]
    Pair _ -> mempty
    Pi1 _ -> mempty
    Pi2 _ -> mempty
    Sum _ -> mempty
    SumListLookup {} -> mempty
    SumMapLength {} -> mempty
    To {} -> mempty
    Top _ -> mempty

getDirectSubformulasAndPairedWitnesses ::
  (ann -> ValidContext 'Local ann) ->
  Term ann ->
  Witness ->
  EvaluationContext ann ->
  Either (ErrorMessage ann) [(Term ann, Witness, EvaluationContext ann)]
getDirectSubformulasAndPairedWitnesses lc x w e =
  case x of
    NamedTerm ann name ->
      case Map.lookup name (lc ann ^. #unValidContext) of
        Just (Defined _ def) ->
          pure [(def, w, die "TODO")]
        Just (FreeVariable _) -> pure mempty
        _ -> die "getDirectSubformulasAndPairedWitnesses: expected the name of a term (this is a compiler bug)"
    AddN _ -> pure mempty
    MulN _ -> pure mempty
    ConstN {} -> pure mempty
    AddZ {} -> pure mempty
    MulZ {} -> pure mempty
    ConstZ {} -> pure mempty
    ConstFp {} -> pure mempty
    AddFp _ -> pure mempty
    MulFp _ -> pure mempty
    Cast _ -> pure mempty
    ConstFin {} -> pure mempty
    ConstF {} -> pure mempty
    ConstSet {} -> pure mempty
    Inverse _ -> pure mempty
    Pair _ -> pure mempty
    Pi1 _ -> pure mempty
    Pi2 _ -> pure mempty
    Iota1 _ -> pure mempty
    Iota2 _ -> pure mempty
    FunctionProduct {} -> pure mempty
    FunctionCoproduct {} -> pure mempty
    Lambda _ann _v _a body -> pure [(body, w, die "TODO")]
    Apply _ann f z -> pure [(f, w), (z, w)]
    To {} -> pure mempty
    From {} -> pure mempty
    Let _ann _v _a _def body -> pure [(body, w)]
    IsNothing _ -> pure mempty
    Just' _ -> pure mempty
    Nothing' _ -> pure mempty
    Maybe' {} -> pure mempty
    MaybePi1 _ -> pure mempty
    MaybePi2 _ -> pure mempty
    MaybeTo {} -> pure mempty
    MaybeFrom {} -> pure mempty
    MaxN _ -> pure mempty
    MaxZ _ -> pure mempty
    MaxFp _ -> pure mempty
    Exists _ -> pure mempty
    Length _ -> pure mempty
    Nth _ -> pure mempty
    ListCast _ -> pure mempty
    ListPi1 _ -> pure mempty
    ListPi2 _ -> pure mempty
    ListTo {} -> pure mempty
    ListFrom {} -> pure mempty
    ListLength _ -> pure mempty
    ListMaybePi1 _ -> pure mempty
    ListMaybePi2 _ -> pure mempty
    ListMaybeLength _ -> pure mempty
    ListMaybeFrom {} -> pure mempty
    ListMaybeTo {} -> pure mempty
    Sum _ -> pure mempty
    Lookup _ -> pure mempty
    Keys _ -> pure mempty
    MapPi1 _ -> pure mempty
    MapPi2 _ -> pure mempty
    MapTo {} -> pure mempty
    MapFrom {} -> pure mempty
    SumMapLength _ -> pure mempty
    SumListLookup {} -> pure mempty
    Equal {} -> pure mempty
    LessOrEqual {} -> pure mempty
    And ann p q -> do
      (pw, qw) <- splitWitness ann w
      pure [(p, pw), (q, qw)]
    Or ann p q -> do
      (pw, qw) <- splitWitness ann w
      pure [(p, pw), (q, qw)]
    Not _ p -> pure [(p, w)]
    Implies ann p q -> do
      (pw, qw) <- splitWitness ann w
      pure [(p, pw), (q, qw)]
    Iff ann p q -> do
      (pw, qw) <- splitWitness ann w
      pure [(p, pw), (q, qw)]
    Top _ -> pure mempty
    Bottom _ -> pure mempty
    ForAll ann v _a _bound p ->
      case Map.lookup v (e ^. #unEvaluationContext) of
        Just (Value vv) ->
          case w of
            Witness (Fun f) ->
              case Map.lookup vv f of
                Just w' -> pure [(p, Witness w')]
                Nothing ->
                  Left . ErrorMessage ann $
                    "witness is undefined for the current evaluation context"
            _ ->
              Left . ErrorMessage ann $
                "witness type does not match context; expected a function"
        Just _ ->
          Left . ErrorMessage ann $
            "universal variable evaluation does not match context; expected a value"
        Nothing ->
          Left . ErrorMessage ann $
            "universal quantifier variable is undefined in the current evaluation context"
    ForSome ann _v _a _bound p ->
      case w of
        Witness (Pair' _vw pw) -> pure [(p, Witness pw)]
        _ ->
          Left . ErrorMessage ann $
            "witness type does not match context; expected a pair"

splitWitness :: ann -> Witness -> Either (ErrorMessage ann) (Witness, Witness)
splitWitness ann =
  \case
    Witness (Pair' w0 w1) -> pure (Witness w0, Witness w1)
    _ -> Left . ErrorMessage ann $ "splitWitness: expected a pair"
