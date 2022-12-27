{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

module OSL.Types.Sigma11
  ( Name (Name),
    PredicateName (PredicateName),
    TermF (..),
    Term,
    var,
    Formula (..),
    ExistentialQuantifier (..),
    someFirstOrder,
    InstanceQuantifier (..),
    InputBound,
    inputBound,
    InputBoundF (..),
    OutputBound,
    OutputBoundF (..),
    Bound,
    BoundF (..),
    Quantifier (ForAll', ForSome', Given'),
    AuxTables (..),
  )
where

import Data.Generics.Labels ()
import Data.List (intercalate)
import Data.Map (Map)
import Data.Set (Set)
import GHC.Generics (Generic)
import OSL.Types.Arity (Arity)
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex)

data Name = Name {arity :: Arity, deBruijnIndex :: DeBruijnIndex}
  deriving (Eq, Ord, Generic)

instance Show Name where
  show (Name a i) = show i <> "^" <> show a

data PredicateName = PredicateName {arity :: Arity, deBruijnIndex :: DeBruijnIndex}
  deriving (Eq, Ord, Generic)

instance Show PredicateName where
  show (PredicateName a i) = "P" <> show i <> "^" <> show a

data TermF name
  = App name [TermF name]
  | AppInverse name (TermF name)
  | Add (TermF name) (TermF name)
  | Mul (TermF name) (TermF name)
  | IndLess (TermF name) (TermF name)
  | Max (TermF name) (TermF name)
  | Const Integer
  deriving (Eq)

type Term = TermF Name

var :: name -> TermF name
var x = App x []

instance Show a => Show (TermF a) where
  show (App name []) = show name
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

data Formula
  = Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName [Term]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll Bound Formula
  | ForSome ExistentialQuantifier Formula
  | Given Cardinality [InputBound] OutputBound Formula
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
  show (ForAll b p) =
    "(∀<" <> show b <> ", " <> show p <> ")"
  show (ForSome q p) =
    "(∃" <> show q <> ", " <> show p <> ")"
  show (Given _ [] ob p) =
    "(λ<" <> show ob <> ", " <> show p <> ")"
  show (Given n ibs ob p) =
    "(λ^" <> show n <> "<" <> show ob <> "(" <> intercalate ", " (show <$> ibs) <> "), " <> show p <> ")"
  show (Predicate p qs) =
    show p <> "(" <> intercalate ", " (show <$> qs) <> ")"
  show Top = "⊤"
  show Bottom = "⊥"

data InputBoundF name
  = UnnamedInputBound {bound :: BoundF name}
  | NamedInputBound {_name :: name, bound :: BoundF name}
  deriving (Eq, Generic)

instance Show a => Show (InputBoundF a) where
  show (UnnamedInputBound b) = "<" <> show b
  show (NamedInputBound x b) = "(" <> show x <> "<" <> show b <> ")"

-- In an input bound, de Bruijn indices refer first to the preceding
-- input argument values, with the last argument having the lowest index,
-- and then to the variables in the scope surrounding the quantifier.
type InputBound = InputBoundF Name

inputBound :: Bound -> InputBound
inputBound = UnnamedInputBound

-- In an output bound, de Bruijn indices refer first to the input
-- argument values, with the last argument having the lowest index,
-- and then to the variables in the scope surrounding the quantifier.
type OutputBound = OutputBoundF Name

newtype OutputBoundF name = OutputBound {unOutputBound :: BoundF name}
  deriving (Eq, Generic)

deriving newtype instance Show a => Show (OutputBoundF a)

data ExistentialQuantifier
  = Some Cardinality [InputBound] OutputBound
  | SomeP Cardinality InputBound OutputBound

someFirstOrder :: Bound -> ExistentialQuantifier
someFirstOrder b =
  Some (Cardinality 1) [] (OutputBound b)

instance Show ExistentialQuantifier where
  show (Some _ [] b) = "<" <> show b
  show (Some (Cardinality n) bs b) =
    "^"
      <> show n
      <> "("
      <> intercalate ", " (show <$> bs)
      <> ")<"
      <> show b
  show (SomeP (Cardinality n) b0 b1) =
    "^"
      <> show n
      <> "<"
      <> show b0
      <> "("
      <> show b1
      <> ")"

data InstanceQuantifier
  = Instance Cardinality [InputBound] OutputBound

data BoundF name = TermBound (TermF name) | FieldMaxBound
  deriving (Eq)

type Bound = BoundF Name

instance Show a => Show (BoundF a) where
  show (TermBound t) = show t
  show FieldMaxBound = "|F|"

data Quantifier
  = ForAll' Bound
  | ForSome' ExistentialQuantifier
  | Given' InstanceQuantifier

data AuxTables = AuxTables
  { functionTables :: Map Name (Map [Integer] Integer),
    predicateTables :: Map PredicateName (Set [Integer])
  }
  deriving (Eq, Show, Generic)

instance Semigroup AuxTables where
  (AuxTables ft0 pt0) <> (AuxTables ft1 pt1) = AuxTables (ft0 <> ft1) (pt0 <> pt1)

instance Monoid AuxTables where
  mempty = AuxTables mempty mempty
