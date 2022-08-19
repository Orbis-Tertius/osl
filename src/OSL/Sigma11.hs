{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module OSL.Sigma11
  ( MapNames (mapNames)
  , incrementDeBruijnIndices
  ) where


import Data.List.NonEmpty (NonEmpty)

import OSL.Types.Arity (Arity)
import OSL.Types.DeBruijnIndex (DeBruijnIndex (..))
import OSL.Types.Sigma11 (Name (..), Term (Var, App, Add, Mul, IndLess, Const), Formula (Equal, LessOrEqual, Not, And, Or, Implies, ForAll, ExistsFO, ExistsSO))
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
      ForAll bound p -> ForAll (mapNames f bound) (mapNames f p)
      ExistsFO bound p -> ExistsFO (mapNames f bound) (mapNames f p)
      ExistsSO outBound inBounds p ->
        ExistsSO (mapNames f outBound) (mapNames f inBounds) (mapNames f p)


instance MapNames a => MapNames (Mapping a) where
  mapNames f = fmap (mapNames f)


incrementDeBruijnIndices :: MapNames a => Arity -> Int -> a -> a
incrementDeBruijnIndices arity b =
  mapNames (\(Name arity' index) ->
    if arity' == arity
    then Name arity' (index + DeBruijnIndex b)
    else Name arity' index)
