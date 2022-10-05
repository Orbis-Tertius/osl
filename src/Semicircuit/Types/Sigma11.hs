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
  , Bound (..)
  , Quantifier (..)
  ) where


import Data.List.NonEmpty (NonEmpty)
import GHC.Generics (Generic)

import OSL.Types.Arity (Arity)
import OSL.Types.Cardinality (Cardinality)
import OSL.Types.Sigma11 (PredicateName)


data Name = Name { arity :: Arity, sym :: Int }
  deriving (Eq, Ord, Generic)


data Term =
    Var Name
  | App Name (NonEmpty Term)
  | AppInverse Name Term
  | Add Term Term
  | Mul Term Term
  | IndLess Term Term
  | Const Integer
  deriving Eq


data Formula =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName (NonEmpty Term)
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll Name Bound Formula
  | Exists ExistentialQuantifier Formula


data ExistentialQuantifier =
    ExistsFO Name Bound
  | ExistsSO Name Cardinality Bound (NonEmpty Bound)
  | ExistsP Name Cardinality Bound Bound


data Bound = TermBound Term | FieldMaxBound
  deriving Eq


data Quantifier =
    Universal Name Bound
  | Existential ExistentialQuantifier
