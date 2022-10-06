{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

module OSL.Sigma11
  ( MapNames (mapNames),
    incrementDeBruijnIndices,
    incrementArities,
    unionIndices,
    termIndices,
    prependBounds,
  )
where

import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import OSL.Types.Arity (Arity (..))
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.Sigma11 (Bound (FieldMaxBound, TermBound), ExistentialQuantifier (Some, SomeP), Formula (And, Equal, ForAll, ForSome, Iff, Implies, LessOrEqual, Not, Or, Predicate), InputBound (..), Name (..), OutputBound (..), Term (Add, App, AppInverse, Const, IndLess, Mul))
import OSL.Types.TranslationContext (Mapping (..))

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
    Const _ -> mempty

prependBounds ::
  Cardinality ->
  [InputBound] ->
  ExistentialQuantifier ->
  ExistentialQuantifier
prependBounds n bs (Some _ [] b) =
  Some n bs b
prependBounds _ bs' (Some n bs b) =
  Some n (bs' <> bs) b
prependBounds _ _ (SomeP {}) =
  error "there is a compiler bug; applied prependBounds to SomeP"
