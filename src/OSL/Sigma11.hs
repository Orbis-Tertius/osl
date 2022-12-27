{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module OSL.Sigma11
  ( MapNames (mapNames),
    incrementDeBruijnIndices,
    incrementArities,
    unionIndices,
    termIndices,
    PrependBounds (prependBounds),
    prependInstanceQuantifiers,
    evalTerm,
    evalFormula,
    boolToScalar,
    scalarValue,
    auxTablesToEvalContext,
    flipQuantifiers,
    flipQuantifier,
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
import OSL.Types.Sigma11 (AuxTables, Bound (FieldMaxBound, TermBound), ExistentialQuantifier (Some, SomeP), Formula (And, Bottom, Equal, ForAll, ForSome, Given, Iff, Implies, LessOrEqual, Not, Or, Predicate, Top), InputBound (..), InstanceQuantifier (Instance), Name (..), OutputBound (..), PredicateName, Quantifier (ForAll', ForSome', Given'), Term (Add, App, AppInverse, Const, IndLess, Max, Mul), someFirstOrder)
import OSL.Types.Sigma11.Argument (Argument (Argument), Statement (Statement), Witness (Witness))
import OSL.Types.Sigma11.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.Sigma11.Value (Value (Value))
import OSL.Types.Sigma11.ValueTree (ValueTree (ValueTree))
import OSL.Types.TranslationContext (Mapping (..))
import Stark.Types.Scalar (Scalar, integerToScalar, one, zero)
import Prelude hiding (fromInteger)

class MapNames a where
  mapNames :: (Name -> Name) -> a -> a

instance MapNames Name where
  mapNames = id

instance MapNames Term where
  mapNames f =
    \case
      App g xs -> App (f g) (mapNames f xs)
      AppInverse g x -> AppInverse (f g) (mapNames f x)
      Add x y -> Add (mapNames f x) (mapNames f y)
      Mul x y -> Mul (mapNames f x) (mapNames f y)
      IndLess x y -> IndLess (mapNames f x) (mapNames f y)
      Max x y -> Max (mapNames f x) (mapNames f y)
      Const x -> Const x

instance MapNames Formula where
  mapNames f =
    \case
      Equal x y -> Equal (mapNames f x) (mapNames f y)
      LessOrEqual x y -> LessOrEqual (mapNames f x) (mapNames f y)
      Predicate p q -> Predicate p (mapNames f q)
      And p q -> And (mapNames f p) (mapNames f q)
      Or p q -> Or (mapNames f p) (mapNames f q)
      Not p -> Not (mapNames f p)
      Implies p q -> Implies (mapNames f p) (mapNames f q)
      Iff p q -> Iff (mapNames f p) (mapNames f q)
      ForAll bound p -> ForAll (mapNames f bound) (mapNames f p)
      ForSome (Some n inBounds outBound) p ->
        ForSome (Some n (mapNames f inBounds) (mapNames f outBound)) (mapNames f p)
      ForSome (SomeP n inBound outBound) p ->
        ForSome (SomeP n (mapNames f inBound) (mapNames f outBound)) (mapNames f p)
      Given n ibs ob p ->
        Given n (mapNames f ibs) (mapNames f ob) (mapNames f p)
      Top -> Top
      Bottom -> Bottom

instance MapNames Bound where
  mapNames f =
    \case
      TermBound t -> TermBound (mapNames f t)
      FieldMaxBound -> FieldMaxBound

deriving newtype instance MapNames InputBound

deriving newtype instance MapNames OutputBound

instance MapNames a => MapNames (Mapping ann a) where
  mapNames f = fmap (mapNames f)

instance MapNames a => MapNames [a] where
  mapNames f = fmap (mapNames f)

incrementArities :: MapNames a => Int -> a -> a
incrementArities by =
  mapNames
    ( \(Name (Arity arity) index) ->
        Name (Arity (arity + by)) index
    )

incrementDeBruijnIndices :: MapNames a => Arity -> Int -> a -> a
incrementDeBruijnIndices arity by =
  mapNames
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

class PrependBounds a where
  prependBounds :: Cardinality -> [InputBound] -> a -> a

instance PrependBounds ExistentialQuantifier where
  prependBounds n bs (Some _ [] b) =
    Some n bs b
  prependBounds _ bs' (Some n bs b) =
    Some n (bs' <> bs) b
  prependBounds _ _ (SomeP {}) =
    die "there is a compiler bug; applied prependBounds to SomeP"

instance PrependBounds InstanceQuantifier where
  prependBounds n bs (Instance _ [] b) =
    Instance n bs b
  prependBounds _ bs' (Instance n bs b) =
    -- TODO: does the cardinality multiply?
    Instance n (bs' <> bs) b

prependInstanceQuantifiers :: [InstanceQuantifier] -> Formula -> Formula
prependInstanceQuantifiers = foldl' (.) id . fmap prependInstanceQuantifier

prependInstanceQuantifier :: InstanceQuantifier -> Formula -> Formula
prependInstanceQuantifier (Instance n bs b) = Given n bs b

evalTerm :: EvaluationContext -> Term -> Either (ErrorMessage ()) Scalar
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
            "name not defined in given evaluation context"
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
  EvaluationContext ->
  Argument ->
  Formula ->
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
    Given n ibs ob p ->
      case arg ^. #statement . #unStatement of
        (i : is') -> do
          let c' = addToEvalContext c (Arity (length ibs)) i
          let arg' = Argument (Statement is') (arg ^. #witness)
          checkValueIsInBounds c n ibs ob i
          evalFormula c' arg' p
        [] -> Left . ErrorMessage () $ "statement is too short"
    ForSome (Some n ibs ob) p ->
      existentialQuantifier n ibs ob p
    ForSome (SomeP n ib ob) p ->
      -- TODO: also check witness value is a permutation
      existentialQuantifier n [ib] ob p
    ForAll FieldMaxBound _ ->
      Left . ErrorMessage () $
        "field max bound unsupported in universal quantifier"
    ForAll (TermBound b) p -> do
      b' <- evalTerm c b
      let go x arg' = do
            let (arg'', arg''') = popArg arg'
                c' =
                  addToEvalContext
                    c
                    (Arity 0)
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

    existentialQuantifier n ibs ob p =
      let arity = Arity (length ibs)
       in case arg ^. #witness . #unWitness of
            ValueTree (Just w) [ws'] -> do
              let c' = addToEvalContext c arity w
                  arg' = Argument (arg ^. #statement) (Witness ws')
              checkValueIsInBounds c n ibs ob w
              evalFormula c' arg' p
            _ ->
              Left . ErrorMessage () $
                "witness has wrong shape for an existential quantifier: " <> pack (show (arg ^. #witness . #unWitness, p))

checkValueIsInBounds ::
  EvaluationContext ->
  Cardinality ->
  [InputBound] ->
  OutputBound ->
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
  EvaluationContext ->
  [(Scalar, InputBound)] ->
  (Scalar, OutputBound) ->
  Either (ErrorMessage ()) ()
checkPointIsInBounds _ [] (_, OutputBound FieldMaxBound) = pure ()
checkPointIsInBounds c [] (y, OutputBound (TermBound ob)) = do
  ob' <- evalTerm c ob
  when (y >= ob') (Left (ErrorMessage () "output is out of bounds"))
checkPointIsInBounds c ((x, InputBound FieldMaxBound) : ibs) (y, ob) = do
  let c' = addToEvalContext c (Arity 0) (scalarValue x)
  checkPointIsInBounds c' ibs (y, ob)
checkPointIsInBounds c ((x, InputBound (TermBound ib)) : ibs) (y, ob) = do
  ib' <- evalTerm c ib
  when (x >= ib') (Left (ErrorMessage () "input is out of bounds"))
  let c' = addToEvalContext c (Arity 0) (scalarValue x)
  checkPointIsInBounds c' ibs (y, ob)

addToEvalContext :: EvaluationContext -> Arity -> Value -> EvaluationContext
addToEvalContext (EvaluationContext c) n x =
  EvaluationContext . Map.insert (Left (Name n 0)) x $
    Map.mapKeys incIfN c
  where
    incIfN (Left (Name n' i)) =
      if n == n'
        then Left (Name n (i + 1))
        else Left (Name n' i)
    incIfN (Right p) = Right p

auxTablesToEvalContext :: AuxTables -> Either (ErrorMessage ()) EvaluationContext
auxTablesToEvalContext aux =
  mconcat
    <$> sequence
      [ functionTablesToEvalContext (aux ^. #functionTables),
        predicateTablesToEvalContext (aux ^. #predicateTables)
      ]

functionTablesToEvalContext ::
  Map Name (Map [Integer] Integer) ->
  Either (ErrorMessage ()) EvaluationContext
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
  Map PredicateName (Set [Integer]) ->
  Either (ErrorMessage ()) EvaluationContext
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
    ForAll b p -> prependQuantifier <$> f (ForAll' b) <*> rec p
    ForSome q p -> prependQuantifier <$> f (ForSome' q) <*> rec p
    Given n ibs ob p -> prependQuantifier <$> f (Given' (Instance n ibs ob)) <*> rec p
    Top -> pure Top
    Bottom -> pure Bottom
  where
    rec = mapQuantifiers f

prependQuantifier :: Quantifier -> Formula -> Formula
prependQuantifier =
  \case
    ForAll' b -> ForAll b
    ForSome' q -> ForSome q
    Given' (Instance n ibs ob) -> Given n ibs ob

flipQuantifier ::
  ann ->
  Quantifier ->
  Either (ErrorMessage ann) Quantifier
flipQuantifier ann =
  \case
    ForAll' b ->
      pure (ForSome' (someFirstOrder b))
    ForSome' (Some _ [] (OutputBound b)) ->
      pure (ForAll' b)
    ForSome' _ ->
      Left . ErrorMessage ann $
        "not supported: second-order quantification in negative position"
    Given' (Instance n ibs ob) ->
      pure (Given' (Instance n ibs ob))
