{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module OSL.Sigma11
  ( MapNames (mapNames)
  , incrementDeBruijnIndices
  , incrementArities
  , unionIndices
  , termIndices
  , prependBounds
  ) where


import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import OSL.Types.Arity (Arity (..))
import OSL.Types.Cardinality (Cardinality)
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.Sigma11 (Name (..), Term (Var, App, Add, Mul, IndLess, Const), Formula (Equal, LessOrEqual, Not, And, Or, Implies, Iff, ForAll, Exists), ExistentialQuantifier (ExistsFO, ExistsSO))
import OSL.Types.TranslationContext (Mapping (..))


class MapNames a where
  mapNames :: (Name -> Name) -> a -> a

instance MapNames Name where
  mapNames = id

instance MapNames Term where
  mapNames f =
    \case
      Var x -> Var (f x)
      App g xs -> App (f g) (mapNames f xs)
      Add x y -> Add (mapNames f x) (mapNames f y)
      Mul x y -> Mul (mapNames f x) (mapNames f y)
      IndLess x y -> IndLess (mapNames f x) (mapNames f y)
      Const x -> Const x

instance MapNames (NonEmpty Term) where
  mapNames f = fmap (mapNames f)

instance MapNames Formula where
  mapNames f =
    \case
      Equal x y -> Equal (mapNames f x) (mapNames f y)
      LessOrEqual x y -> LessOrEqual (mapNames f x) (mapNames f y)
      And p q -> And (mapNames f p) (mapNames f q)
      Or p q -> Or (mapNames f p) (mapNames f q)
      Not p -> Not (mapNames f p)
      Implies p q -> Implies (mapNames f p) (mapNames f q)
      Iff p q -> Iff (mapNames f p) (mapNames f q)
      ForAll bound p -> ForAll (mapNames f bound) (mapNames f p)
      Exists (ExistsFO bound) p ->
        Exists (ExistsFO (mapNames f bound)) (mapNames f p)
      Exists (ExistsSO n outBound inBounds) p ->
        Exists (ExistsSO n (mapNames f outBound) (mapNames f inBounds)) (mapNames f p)


instance MapNames a => MapNames (Mapping ann a) where
  mapNames f = fmap (mapNames f)


incrementArities :: MapNames a => Int -> a -> a
incrementArities by =
  mapNames
  (\(Name (Arity arity) index) ->
     Name (Arity (arity + by)) index)


incrementDeBruijnIndices :: MapNames a => Arity -> Int -> a -> a
incrementDeBruijnIndices arity by =
  mapNames (\(Name arity' index) ->
    if arity' == arity
    then Name arity' (index + DeBruijnIndex by)
    else Name arity' index)


unionIndices
  :: Map Arity (Set DeBruijnIndex)
  -> Map Arity (Set DeBruijnIndex)
  -> Map Arity (Set DeBruijnIndex)
unionIndices = Map.unionWith Set.union


termIndices :: Term -> Map Arity (Set DeBruijnIndex)
termIndices =
  \case
    Var (Name arity i) ->
      Map.singleton arity (Set.singleton i)
    App (Name fArity fIndex) x ->
      Map.singleton fArity (Set.singleton fIndex)
        `unionIndices`
        (foldl' unionIndices mempty
          (termIndices <$> x))
    Add x y -> termIndices x `unionIndices` termIndices y
    Mul x y -> termIndices x `unionIndices` termIndices y
    IndLess x y -> termIndices x `unionIndices` termIndices y
    Const _ -> mempty


prependBounds
  :: Maybe Cardinality
  -> [Term]
  -> ExistentialQuantifier
  -> ExistentialQuantifier
prependBounds n bs (ExistsFO b) =
  case NonEmpty.nonEmpty bs of
    Just bs' -> ExistsSO n b bs'
    Nothing -> ExistsFO b
prependBounds _ bs' (ExistsSO n b bs) =
  case NonEmpty.nonEmpty bs' of
    Just bs'' -> ExistsSO n b (bs'' <> bs)
    Nothing -> ExistsSO n b bs
