{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module OSL.Sigma11
  ( incrementDeBruijnIndices,
    incrementArities,
    HasIncrementArity (incrementArity),
    unionIndices,
    termIndices,
    HasPrependBounds (prependBounds),
    prependInstanceQuantifiers,
    evalTerm,
    evalFormula,
    boolToScalar,
    scalarValue,
    auxTablesToEvalContext,
    flipQuantifiers,
    flipQuantifier,
    prependQuantifier,
    prependQuantifiers,
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger)
import Control.Lens ((^.))
import Control.Monad (forM_, when)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (pack)
import Die (die)
import OSL.Types.Arity (Arity (..))
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.Sigma11 (AuxTablesF, BoundF (FieldMaxBound, TermBound), ExistentialQuantifierF (Some, SomeP), Formula, FormulaF (And, Bottom, Equal, ForAll, ForSome, Given, Iff, Implies, LessOrEqual, Not, Or, Predicate, Top), InputBoundF (..), InstanceQuantifierF (Instance), Name (..), OutputBoundF (..), PredicateName, Quantifier, QuantifierF (ForAll', ForSome', Given'), Term, TermF (Add, App, AppInverse, Const, IndLess, Max, Mul))
import OSL.Types.Sigma11.Argument (Argument (Argument), Statement (Statement), Witness (Witness))
import OSL.Types.Sigma11.EvaluationContext (EvaluationContextF (EvaluationContext))
import OSL.Types.Sigma11.Value (Value (Value))
import OSL.Types.Sigma11.ValueTree (ValueTree (ValueTree))
import Stark.Types.Scalar (Scalar, integerToScalar, one, zero)
import Prelude hiding (fromInteger)

class HasIncrementArity name where
  incrementArity :: Int -> name -> name

instance HasIncrementArity Name where
  incrementArity by (Name (Arity arity) index) =
    Name (Arity (arity + by)) index

incrementArities ::
  Functor f =>
  HasIncrementArity name =>
  Int ->
  f name ->
  f name
incrementArities by =
  fmap (incrementArity by)

incrementDeBruijnIndices :: Functor f => Arity -> Int -> f Name -> f Name
incrementDeBruijnIndices arity by =
  fmap
    ( \(Name arity' index) ->
        if arity' == arity
          then Name arity' (index + DeBruijnIndex by)
          else Name arity' index
    )

unionIndices ::
  Map Arity (Set DeBruijnIndex) ->
  Map Arity (Set DeBruijnIndex) ->
  Map Arity (Set DeBruijnIndex)
unionIndices = Map.unionWith Set.union

termIndices :: Term -> Map Arity (Set DeBruijnIndex)
termIndices =
  \case
    App (Name fArity fIndex) x ->
      Map.singleton fArity (Set.singleton fIndex)
        `unionIndices` foldl'
          unionIndices
          mempty
          (termIndices <$> x)
    AppInverse (Name fArity fIndex) x ->
      Map.singleton fArity (Set.singleton fIndex)
        `unionIndices` termIndices x
    Add x y -> termIndices x `unionIndices` termIndices y
    Mul x y -> termIndices x `unionIndices` termIndices y
    IndLess x y -> termIndices x `unionIndices` termIndices y
    Max x y -> termIndices x `unionIndices` termIndices y
    Const _ -> mempty

class HasPrependBounds f where
  prependBounds :: HasIncrementArity name => Cardinality -> [InputBoundF name] -> f name -> f name

instance HasPrependBounds ExistentialQuantifierF where
  prependBounds n bs (Some x _ [] b) =
    Some (incrementArity (length bs) x) n bs b
  prependBounds _ bs' (Some x n bs b) =
    Some (incrementArity (length bs) x) n (bs' <> bs) b
  prependBounds _ _ (SomeP {}) =
    die "there is a compiler bug; applied prependBounds to SomeP"

instance HasPrependBounds InstanceQuantifierF where
  prependBounds n bs (Instance x _ [] b) =
    Instance (incrementArity (length bs) x) n bs b
  prependBounds _ bs' (Instance x n bs b) =
    -- TODO: does the cardinality multiply?
    Instance (incrementArity (length bs) x) n (bs' <> bs) b

prependInstanceQuantifiers ::
  [InstanceQuantifierF name] ->
  FormulaF name ->
  FormulaF name
prependInstanceQuantifiers =
  foldl' (.) id . fmap prependInstanceQuantifier

prependInstanceQuantifier ::
  InstanceQuantifierF name ->
  FormulaF name ->
  FormulaF name
prependInstanceQuantifier (Instance x n bs b) = Given x n bs b

evalTerm ::
  (Show name, Ord name) =>
  EvaluationContextF name ->
  TermF name ->
  Either (ErrorMessage ()) Scalar
evalTerm (EvaluationContext c) =
  \case
    App f xs ->
      case Map.lookup (Left f) c of
        Just (Value f') -> do
          xs' <- mapM rec xs
          case Map.lookup xs' f' of
            Just y -> pure y
            Nothing ->
              Left . ErrorMessage () $
                "value not defined on given inputs: " <> pack (show (xs', f'))
        Nothing ->
          Left . ErrorMessage () $
            "name not defined in given evaluation context: "
              <> pack (show (f, c))
    AppInverse f x ->
      case Map.lookup (Left f) c of
        Just (Value f') -> do
          x' <- rec x
          case Map.keys (Map.filter (== x') f') of
            [[y]] -> pure y
            [] ->
              Left . ErrorMessage () $
                "function inverse not defined on given input"
            _ ->
              Left . ErrorMessage () $
                "function does not have a unique inverse on given input"
        Nothing ->
          Left . ErrorMessage () $
            "name not defined in given evaluation context"
    Add x y -> (Group.+) <$> rec x <*> rec y
    Mul x y -> (Ring.*) <$> rec x <*> rec y
    IndLess x y -> boolToScalar <$> ((<=) <$> rec x <*> rec y)
    Max x y -> max <$> rec x <*> rec y
    Const i ->
      case integerToScalar i of
        Just i' -> pure i'
        Nothing ->
          Left . ErrorMessage () $
            "constant out of range of scalar field"
  where
    rec = evalTerm (EvaluationContext c)

boolToScalar :: Bool -> Scalar
boolToScalar True = one
boolToScalar False = zero

evalFormula ::
  (Show name, Ord name, HasAddToEvalContext name) =>
  EvaluationContextF name ->
  Argument ->
  FormulaF name ->
  Either (ErrorMessage ()) Bool
evalFormula c arg =
  \case
    Equal x y ->
      (==) <$> evalTerm c x <*> evalTerm c y
    LessOrEqual x y ->
      (<=) <$> evalTerm c x <*> evalTerm c y
    Predicate p xs -> do
      xs' <- mapM (evalTerm c) xs
      case Map.lookup (Right p) (c ^. #unEvaluationContext) of
        Just (Value p') ->
          maybe
            (pure False)
            (const (pure True))
            (Map.lookup xs' p')
        Nothing ->
          Left . ErrorMessage () $
            "predicate not defined in given evaluation context"
    Not p -> not <$> rec arg p
    And p q -> do
      let (arg0, arg1) = splitArg
      (&&) <$> rec arg0 p <*> rec arg1 q
    Or p q -> do
      let (arg0, arg1) = splitArg
      (||) <$> rec arg0 p <*> rec arg1 q
    Implies p q -> do
      let (arg0, arg1) = splitArg
      (||) <$> (not <$> rec arg0 p) <*> rec arg1 q
    Iff p q -> do
      let (arg0, arg1) = splitArg
      (==) <$> rec arg0 p <*> rec arg1 q
    Top -> pure True
    Bottom -> pure False
    Given v n ibs ob p ->
      case arg ^. #statement . #unStatement of
        (i : is') -> do
          let c' = addToEvalContext c (Left v) i
          let arg' = Argument (Statement is') (arg ^. #witness)
          checkValueIsInBounds c n ibs ob i
          evalFormula c' arg' p
        [] -> Left . ErrorMessage () $ "statement is too short"
    ForSome (Some v n ibs ob) p ->
      existentialQuantifier v n ibs ob p
    ForSome (SomeP v n ib ob) p ->
      -- TODO: also check witness value is a permutation
      existentialQuantifier v n [ib] ob p
    ForAll _ FieldMaxBound _ ->
      Left . ErrorMessage () $
        "field max bound unsupported in universal quantifier"
    ForAll v (TermBound b) p -> do
      b' <- evalTerm c b
      let go x arg' = do
            let (arg'', arg''') = popArg arg'
                c' =
                  addToEvalContext
                    c
                    (Left v)
                    (scalarValue x)
                x' = x Group.+ one
            r <- evalFormula c' arg'' p
            if r
              then
                if x' == b'
                  then pure True
                  else go x' arg'''
              else pure False
      if b' == zero then pure True else go zero arg
  where
    rec = evalFormula c

    splitArg =
      case arg ^. #witness of
        Witness (ValueTree Nothing [w0, w1]) ->
          ( Argument (arg ^. #statement) (Witness w0),
            Argument (arg ^. #statement) (Witness w1)
          )
        _ ->
          ( Argument (arg ^. #statement) (Witness (ValueTree Nothing [])),
            Argument (arg ^. #statement) (Witness (ValueTree Nothing []))
          )

    popArg :: Argument -> (Argument, Argument)
    popArg arg' =
      case arg' ^. #witness . #unWitness . #branches of
        (b : bs) ->
          ( Argument (arg ^. #statement) (Witness b),
            Argument (arg ^. #statement) (Witness (ValueTree Nothing bs))
          )
        [] ->
          ( Argument (arg ^. #statement) (Witness (ValueTree Nothing [])),
            Argument (arg ^. #statement) (Witness (ValueTree Nothing []))
          )

    existentialQuantifier v n ibs ob p =
      case arg ^. #witness . #unWitness of
        ValueTree (Just w) [ws'] -> do
          let c' = addToEvalContext c (Left v) w
              arg' = Argument (arg ^. #statement) (Witness ws')
          checkValueIsInBounds c n ibs ob w
          evalFormula c' arg' p
        _ ->
          Left . ErrorMessage () $
            "witness has wrong shape for an existential quantifier: " <> pack (show (arg ^. #witness . #unWitness, p))

checkValueIsInBounds ::
  (Show name, Ord name, HasAddToEvalContext name) =>
  EvaluationContextF name ->
  Cardinality ->
  [InputBoundF name] ->
  OutputBoundF name ->
  Value ->
  Either (ErrorMessage ()) ()
checkValueIsInBounds c (Cardinality n) ibs ob (Value v) =
  if intToInteger (Map.size v) <= n
    then forM_ (Map.toList v) $ \(xs, y) ->
      if length xs == length ibs
        then do
          checkPointIsInBounds c (zip xs ibs) (y, ob)
        else Left (ErrorMessage () "point has wrong number of inputs")
    else Left (ErrorMessage () ("value is too big: " <> pack (show (Map.size v)) <> " > " <> pack (show n)))

checkPointIsInBounds ::
  (Show name, Ord name, HasAddToEvalContext name) =>
  EvaluationContextF name ->
  [(Scalar, InputBoundF name)] ->
  (Scalar, OutputBoundF name) ->
  Either (ErrorMessage ()) ()
checkPointIsInBounds _ [] (_, OutputBound FieldMaxBound) = pure ()
checkPointIsInBounds c [] (y, OutputBound (TermBound ob)) = do
  ob' <- evalTerm c ob
  when (y >= ob') (Left (ErrorMessage () "output is out of bounds"))
checkPointIsInBounds c ((x, NamedInputBound nm FieldMaxBound) : ibs) (y, ob) = do
  let c' = addToEvalContext c (Left nm) (scalarValue x)
  checkPointIsInBounds c' ibs (y, ob)
checkPointIsInBounds c ((_, UnnamedInputBound FieldMaxBound) : ibs) (y, ob) =
  checkPointIsInBounds c ibs (y, ob)
checkPointIsInBounds c ((x, NamedInputBound nm (TermBound ib)) : ibs) (y, ob) = do
  ib' <- evalTerm c ib
  when (x >= ib') (Left (ErrorMessage () "input is out of bounds"))
  let c' = addToEvalContext c (Left nm) (scalarValue x)
  checkPointIsInBounds c' ibs (y, ob)
checkPointIsInBounds c ((x, UnnamedInputBound (TermBound ib)) : ibs) (y, ob) = do
  ib' <- evalTerm c ib
  when (x >= ib') (Left (ErrorMessage () "input is out of bounds"))
  checkPointIsInBounds c ibs (y, ob)

class HasAddToEvalContext name where
  addToEvalContext :: EvaluationContextF name -> Either name PredicateName -> Value -> EvaluationContextF name

instance HasAddToEvalContext Name where
  addToEvalContext (EvaluationContext c) (Left (Name n 0)) x =
    EvaluationContext . Map.insert (Left (Name (n :: Arity) 0)) x $
      Map.mapKeys incIfN c
    where
      incIfN (Left (Name n' i)) =
        if n == n'
          then Left (Name n (i + 1))
          else Left (Name n' i)
      incIfN (Right p) = Right p
  addToEvalContext _ (Left (Name _ _)) _ = die "OSL.Sigma11.addToEvalContext: tried to add a name with a non-zero de Bruijn index (this is a compiler bug)"
  addToEvalContext (EvaluationContext c) (Right p) x =
    EvaluationContext (Map.insert (Right p) x c)

auxTablesToEvalContext ::
  Ord name =>
  AuxTablesF name ->
  Either (ErrorMessage ()) (EvaluationContextF name)
auxTablesToEvalContext aux =
  mconcat
    <$> sequence
      [ functionTablesToEvalContext (aux ^. #functionTables),
        predicateTablesToEvalContext (aux ^. #predicateTables)
      ]

functionTablesToEvalContext ::
  Ord name =>
  Map name (Map [Integer] Integer) ->
  Either (ErrorMessage ()) (EvaluationContextF name)
functionTablesToEvalContext m =
  EvaluationContext . Map.fromList
    <$> sequence
      [ (Left fName,) . Value . Map.fromList
          <$> sequence
            [ (,) <$> mapM fromInteger xs <*> fromInteger y
              | (xs, y) <- Map.toList f
            ]
        | (fName, f) <- Map.toList m
      ]

predicateTablesToEvalContext ::
  Ord name =>
  Map PredicateName (Set [Integer]) ->
  Either (ErrorMessage ()) (EvaluationContextF name)
predicateTablesToEvalContext m =
  EvaluationContext . Map.fromList
    <$> sequence
      [ (Right pName,) . Value . Map.fromList
          <$> sequence
            [ (,zero) <$> mapM fromInteger xs
              | xs <- Set.toList p
            ]
        | (pName, p) <- Map.toList m
      ]

fromInteger :: Integer -> Either (ErrorMessage ()) Scalar
fromInteger = maybe (Left (ErrorMessage () "integer out of range of scalar field")) pure . integerToScalar

scalarValue :: Scalar -> Value
scalarValue = Value . Map.singleton []

flipQuantifiers ::
  ann ->
  Formula ->
  Either (ErrorMessage ann) Formula
flipQuantifiers ann = mapQuantifiers (flipQuantifier ann)

mapQuantifiers ::
  Monad m =>
  (Quantifier -> m Quantifier) ->
  Formula ->
  m Formula
mapQuantifiers f =
  \case
    Equal x y -> pure (Equal x y)
    LessOrEqual x y -> pure (LessOrEqual x y)
    Predicate p xs -> pure (Predicate p xs)
    Not p -> Not <$> rec p
    And p q -> And <$> rec p <*> rec q
    Or p q -> Or <$> rec p <*> rec q
    Implies p q -> Implies <$> rec p <*> rec q
    Iff p q -> Iff <$> rec p <*> rec q
    ForAll x b p -> prependQuantifier <$> f (ForAll' x b) <*> rec p
    ForSome q p -> prependQuantifier <$> f (ForSome' q) <*> rec p
    Given x n ibs ob p -> prependQuantifier <$> f (Given' (Instance x n ibs ob)) <*> rec p
    Top -> pure Top
    Bottom -> pure Bottom
  where
    rec = mapQuantifiers f

prependQuantifiers :: [QuantifierF name] -> FormulaF name -> FormulaF name
prependQuantifiers qs f =
  foldl' (flip prependQuantifier) f qs

prependQuantifier :: QuantifierF name -> FormulaF name -> FormulaF name
prependQuantifier =
  \case
    ForAll' x b -> ForAll x b
    ForSome' q -> ForSome q
    Given' (Instance x n ibs ob) -> Given x n ibs ob

flipQuantifier ::
  ann ->
  QuantifierF name ->
  Either (ErrorMessage ann) (QuantifierF name)
flipQuantifier ann =
  \case
    ForAll' x b ->
      pure (ForSome' (Some x (1 :: Cardinality) [] (OutputBound b)))
    ForSome' (Some x _ [] (OutputBound b)) ->
      pure (ForAll' x b)
    ForSome' _ ->
      Left . ErrorMessage ann $
        "not supported: second-order quantification in negative position"
    Given' (Instance x n ibs ob) ->
      pure (Given' (Instance x n ibs ob))
