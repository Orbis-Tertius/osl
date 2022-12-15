{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

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
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Control.Lens ((^.))
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Die (die)
import OSL.Types.Arity (Arity (..))
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.Sigma11 (Bound (FieldMaxBound, TermBound), ExistentialQuantifier (Some, SomeP), Formula (And, Bottom, Equal, ForAll, ForSome, Given, Iff, Implies, LessOrEqual, Not, Or, Predicate, Top), InputBound (..), InstanceQuantifier (Instance), Name (..), OutputBound (..), Term (Add, App, AppInverse, Const, IndLess, Max, Mul))
import OSL.Types.Sigma11.Argument (Argument (Argument), Statement (Statement), Witness (Witness))
import OSL.Types.Sigma11.EvaluationContext (EvaluationContext (EvaluationContext))
import OSL.Types.Sigma11.Value (Value (Value))
import OSL.Types.TranslationContext (Mapping (..))
import Stark.Types.Scalar (Scalar, zero, one, integerToScalar)

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
            Nothing -> Left . ErrorMessage () $
              "value not defined on given inputs"
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
        Nothing -> Left . ErrorMessage () $
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
           maybe (pure False) (const (pure True))
             (Map.lookup xs' p')
         Nothing ->
           Left . ErrorMessage () $
             "predicate not defined in given evaluation context"
    Not p -> not <$> rec p
    And p q -> (&&) <$> rec p <*> rec q
    Or p q -> (||) <$> rec p <*> rec q
    Implies p q -> (||) <$> (not <$> rec p) <*> rec q
    Iff p q -> (==) <$> rec p <*> rec q
    Top -> pure True
    Bottom -> pure False
    Given _n ibs _ob p ->
      -- TODO: verify value is in bounds
      case arg ^. #statement . #unStatement of
        (i:is') -> do
          let c' = addToEvalContext c (Arity (length ibs)) i
          let arg' = Argument (Statement is') (arg ^. #witness)
          evalFormula c' arg' p
        [] -> Left . ErrorMessage () $ "statement is too short"
    ForSome (Some _n ibs _ob) p ->
      -- TODO: verify value is in bounds
      existentialQuantifier (Arity (length ibs)) p
    ForSome (SomeP {}) p ->
      -- TODO: verify value is in bounds
      existentialQuantifier (Arity 1) p
    ForAll FieldMaxBound _ ->
      Left . ErrorMessage () $
        "field max bound unsupported in universal quantifier"
    ForAll (TermBound b) p -> do
      b' <- evalTerm c b
      let go x = do
            let c' = addToEvalContext c (Arity 0)
                       (Value (Map.singleton [] x))
                x' = x Group.+ one
            r <- evalFormula c' arg p
            if r && x' == b'
              then pure True
              else if r
                   then go x'
                   else pure False
      go zero
  where
    rec = evalFormula c arg

    existentialQuantifier arity p =
      case arg ^. #witness . #unWitness of
        (w:ws') -> do
          let c' = addToEvalContext c arity w
          let arg' = Argument (arg ^. #statement) (Witness ws')
          evalFormula c' arg' p
        [] -> Left . ErrorMessage () $
          "witness is too short"

addToEvalContext :: EvaluationContext -> Arity -> Value -> EvaluationContext
addToEvalContext (EvaluationContext c) n x =
  EvaluationContext . Map.insert (Left (Name n 0)) x
    $ Map.mapKeys incIfN c
  where
    incIfN (Left (Name n' i)) =
      if n == n'
      then Left (Name n (i+1))
      else Left (Name n' i)
    incIfN (Right p) = Right p
