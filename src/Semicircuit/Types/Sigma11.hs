{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLabels #-}

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
  ( Name (Name),
    Term (..),
    var,
    Formula (..),
    ExistentialQuantifier (..),
    someFirstOrder,
    Bound (..),
    InputBound (..),
    OutputBound (..),
    Quantifier (..),
    MapNames (..),
    EvaluationContext (..),
  )
where

import Control.Lens ((^.))
import Data.List (intercalate)
import Data.Map (Map)
import GHC.Generics (Generic)
import OSL.Types.Arity (Arity)
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.Sigma11 (PredicateName)
import OSL.Types.Sigma11.Value (Value)

data Name = Name {arity :: Arity, sym :: Int}
  deriving (Eq, Ord, Generic)

instance Show Name where
  show x = "x^" <> show (x ^. #arity) <> "_" <> show (x ^. #sym)

class MapNames a where
  mapNames :: (Name -> Name) -> a -> a

instance MapNames a => MapNames [a] where
  mapNames f = fmap (mapNames f)

data Term
  = App Name [Term]
  | AppInverse Name Term
  | Add Term Term
  | Mul Term Term
  | IndLess Term Term
  | Max Term Term
  | Const Integer
  deriving (Eq, Ord)

instance Show Term where
  show (App x []) = show x
  show (App f xs) =
    show f <> "(" <> intercalate ", " (show <$> xs) <> ")"
  show (AppInverse f x) =
    show f <> "^-1(" <> show x <> ")"
  show (Add x y) =
    "(" <> show x <> " + " <> show y <> ")"
  show (Mul x y) =
    "(" <> show x <> " * " <> show y <> ")"
  show (IndLess x y) =
    "ind_<(" <> show x <> ", " <> show y <> ")"
  show (Max x y) =
    "max(" <> show x <> ", " <> show y <> ")"
  show (Const x) = show x

var :: Name -> Term
var x = App x []

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
  mapNames f (Max x y) =
    Max (mapNames f x) (mapNames f y)
  mapNames _ (Const i) = Const i

data Formula
  = Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName [Term]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll Name Bound Formula
  | ForSome ExistentialQuantifier Formula
  | Given Name Cardinality [InputBound] OutputBound Formula
  | Top
  | Bottom

instance Show Formula where
  show (Equal x y) =
    "(" <> show x <> " = " <> show y <> ")"
  show (LessOrEqual x y) =
    "(" <> show x <> " <= " <> show y <> ")"
  show (Not p) = "!" <> show p
  show (And p q) =
    "(" <> show p <> " & " <> show q <> ")"
  show (Or p q) =
    "(" <> show p <> " | " <> show q <> ")"
  show (Implies p q) =
    "(" <> show p <> " -> " <> show q <> ")"
  show (Iff p q) =
    "(" <> show p <> " <-> " <> show q <> ")"
  show (ForAll x b p) =
    "(∀" <> show x <> "<" <> show b <> ", " <> show p <> ")"
  show (ForSome q p) =
    "(∃" <> show q <> ", " <> show p <> ")"
  show (Given x _ [] ob p) =
    "(λ" <> show x <> "<" <> show ob <> "," <> show p <> ")"
  show (Given x n ibs ob p) =
    "(λ" <> show x <> "^" <> show n <> "(" <> intercalate ", " (show <$> ibs)
      <> ")<"
      <> show ob
      <> ", "
      <> show p
      <> ")"
  show (Predicate p qs) =
    show p <> "(" <> intercalate ", " (show <$> qs) <> ")"
  show Top = "⊤"
  show Bottom = "⊥"

data ExistentialQuantifier
  = Some Name Cardinality [InputBound] OutputBound
  | SomeP Name Cardinality InputBound OutputBound
  deriving (Eq)

instance Show ExistentialQuantifier where
  show (Some x _ [] b) = show x <> "<" <> show b
  show (Some x (Cardinality n) bs b) =
    show x <> "^"
      <> show n
      <> "<"
      <> show b
      <> "("
      <> intercalate ", " (("<" <>) . show <$> bs)
      <> ")"
  show (SomeP x (Cardinality n) b0 b1) =
    show x <> "^"
      <> show n
      <> "<"
      <> show b0
      <> "(<"
      <> show b1
      <> ")"

someFirstOrder :: Name -> Bound -> ExistentialQuantifier
someFirstOrder x b =
  Some x (Cardinality 0) [] (OutputBound b)

data Bound = TermBound Term | FieldMaxBound
  deriving (Eq)

instance Show Bound where
  show (TermBound x) = show x
  show FieldMaxBound = "|F|"

data InputBound
  = NamedInputBound {_name :: Name, bound :: Bound}
  | UnnamedInputBound {bound :: Bound}
  deriving (Eq, Generic)

instance Show InputBound where
  show (NamedInputBound name b) =
    show name <> "<" <> show b
  show (UnnamedInputBound b) =
    "<" <> show b

newtype OutputBound = OutputBound {unOutputBound :: Bound}
  deriving stock (Eq, Generic)
  deriving newtype (Show)

data Quantifier
  = Universal Name Bound
  | Existential ExistentialQuantifier
  | Instance Name Cardinality [InputBound] OutputBound

instance Show Quantifier where
  show (Universal x b) = "∀" <> show x <> "<" <> show b
  show (Existential q) = "∃" <> show q
  show (Instance x n ibs ob) =
    "λ" <> show x
      <> ( if null ibs
             then ""
             else "^" <> show n <> "(" <> intercalate ", " (show <$> ibs) <> ")"
         )
      <> "<"
      <> show ob

newtype EvaluationContext = EvaluationContext
  { unEvaluationContext ::
      Map (Either Name PredicateName) Value
  }
