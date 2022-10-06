{-# LANGUAGE DeriveGeneric #-}


-- This is different from OSL.Types.Sigma11
-- in that the types in this module use explicit
-- variable names rather than de Bruijn indices.
-- This is more convenient for conversion to
-- prenex normal forms.
--
-- You might ask, why not just let the types in
-- OSL.Types.Sigma11 be parameterized by the
-- type of names? The reason is that in
-- OSL.Types.Sigma11, the variable names are implied
-- in quantifiers, whereas in this module, the
-- variable names are given explicitly in quantifiers.

module Semicircuit.Types.Sigma11
  ( Name (Name)
  , Term (..)
  , Formula (..)
  , ExistentialQuantifier (..)
  , someFirstOrder
  , Bound (..)
  , InputBound (..)
  , OutputBound (..)
  , Quantifier (..)
  , MapNames (..)
  ) where


import GHC.Generics (Generic)

import OSL.Types.Arity (Arity)
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.Sigma11 (PredicateName)


data Name = Name { arity :: Arity, sym :: Int }
  deriving (Eq, Ord, Generic)


class MapNames a where
  mapNames :: (Name -> Name) -> a -> a

instance MapNames a => MapNames [a] where
  mapNames f = fmap (mapNames f)


data Term =
    App Name [Term]
  | AppInverse Name Term
  | Add Term Term
  | Mul Term Term
  | IndLess Term Term
  | Const Integer
  deriving Eq

instance MapNames Term where
  mapNames f (App g xs) =
    App (f g) (mapNames f <$> xs)
  mapNames f (AppInverse g x) =
    AppInverse (f g) (mapNames f x)
  mapNames f (Add x y) =
    Add (mapNames f x) (mapNames f y)
  mapNames f (Mul x y) =
    Mul (mapNames f x) (mapNames f y)
  mapNames f (IndLess x y) =
    IndLess (mapNames f x) (mapNames f y)
  mapNames _ (Const i) = Const i


data Formula =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName [Term]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll Name Bound Formula
  | ForSome ExistentialQuantifier Formula


data ExistentialQuantifier =
    Some Name Cardinality [InputBound] OutputBound
  | SomeP Name Cardinality InputBound OutputBound


someFirstOrder :: Name -> Bound -> ExistentialQuantifier
someFirstOrder x b =
  Some x (Cardinality 0) [] (OutputBound b)


data Bound = TermBound Term | FieldMaxBound
  deriving Eq


data InputBound =
  InputBound
  { name :: Name
  , bound :: Bound }
  deriving Eq


newtype OutputBound =
  OutputBound { unOutputBound :: Bound}
  deriving Eq


data Quantifier =
    Universal Name Bound
  | Existential ExistentialQuantifier
