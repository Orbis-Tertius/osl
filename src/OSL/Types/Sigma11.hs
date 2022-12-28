{-# LANGUAGE DeriveFunctor #-}
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
    FormulaF (..),
    Formula,
    ExistentialQuantifierF (..),
    ExistentialQuantifier,
    someFirstOrder,
    InstanceQuantifierF (..),
    InstanceQuantifier,
    InputBound,
    inputBound,
    InputBoundF (..),
    OutputBound,
    OutputBoundF (..),
    Bound,
    BoundF (..),
    Quantifier,
    QuantifierF (ForAll', ForSome', Given'),
    AuxTablesF (..),
    AuxTables,
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
  deriving (Eq, Functor)

type Term = TermF Name

var :: name -> TermF name
var x = App x []

instance Show a => Show (TermF a) where
  show (App nm []) = show nm
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

data FormulaF name
  = Equal (TermF name) (TermF name)
  | LessOrEqual (TermF name) (TermF name)
  | Predicate PredicateName [TermF name]
  | Not (FormulaF name)
  | And (FormulaF name) (FormulaF name)
  | Or (FormulaF name) (FormulaF name)
  | Implies (FormulaF name) (FormulaF name)
  | Iff (FormulaF name) (FormulaF name)
  | ForAll name (BoundF name) (FormulaF name)
  | ForSome (ExistentialQuantifierF name) (FormulaF name)
  | Given name Cardinality [InputBoundF name] (OutputBoundF name) (FormulaF name)
  | Top
  | Bottom
  deriving (Functor)

instance Show name => Show (FormulaF name) where
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
  show (ForAll _ b p) =
    "(∀<" <> show b <> ", " <> show p <> ")"
  show (ForSome q p) =
    "(∃" <> show q <> ", " <> show p <> ")"
  show (Given _ _ [] ob p) =
    "(λ<" <> show ob <> ", " <> show p <> ")"
  show (Given _ n ibs ob p) =
    "(λ^" <> show n <> "<" <> show ob <> "(" <> intercalate ", " (show <$> ibs) <> "), " <> show p <> ")"
  show (Predicate p qs) =
    show p <> "(" <> intercalate ", " (show <$> qs) <> ")"
  show Top = "⊤"
  show Bottom = "⊥"

type Formula = FormulaF Name

data InputBoundF name
  = UnnamedInputBound {bound :: BoundF name}
  | NamedInputBound {_name :: name, bound :: BoundF name}
  deriving (Eq, Generic, Functor)

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
  deriving (Eq, Generic, Functor)

deriving newtype instance Show a => Show (OutputBoundF a)

data ExistentialQuantifierF name
  = Some name Cardinality [InputBoundF name] (OutputBoundF name)
  | SomeP name Cardinality (InputBoundF name) (OutputBoundF name)
  deriving (Eq, Functor)

type ExistentialQuantifier = ExistentialQuantifierF Name

someFirstOrder :: Bound -> ExistentialQuantifier
someFirstOrder b =
  Some (Name (0 :: Arity) (0 :: DeBruijnIndex)) (Cardinality 1) [] (OutputBound b)

instance Show name => Show (ExistentialQuantifierF name) where
  show (Some _ _ [] b) = "<" <> show b
  show (Some _ (Cardinality n) bs b) =
    "^"
      <> show n
      <> "("
      <> intercalate ", " (show <$> bs)
      <> ")<"
      <> show b
  show (SomeP _ (Cardinality n) b0 b1) =
    "^"
      <> show n
      <> "<"
      <> show b0
      <> "("
      <> show b1
      <> ")"

data InstanceQuantifierF name
  = Instance { name :: name,
      cardinality :: Cardinality,
      inputBounds :: [InputBoundF name],
      outputBounds :: (OutputBoundF name)
     }
  deriving (Eq, Functor, Generic)

instance Show name => Show (InstanceQuantifierF name) where
  show (Instance _ (Cardinality n) bs b) =
    "^"
      <> show n
      <> "("
      <> intercalate ", " (show <$> bs)
      <> ")<"
      <> show b

type InstanceQuantifier = InstanceQuantifierF Name

data BoundF name = TermBound (TermF name) | FieldMaxBound
  deriving (Eq, Functor)

type Bound = BoundF Name

instance Show a => Show (BoundF a) where
  show (TermBound t) = show t
  show FieldMaxBound = "|F|"

data QuantifierF name
  = ForAll' name (BoundF name)
  | ForSome' (ExistentialQuantifierF name)
  | Given' (InstanceQuantifierF name)
  deriving Functor

instance Show name => Show (QuantifierF name) where
  show (ForAll' x b) = "∀" <> show x <> "<" <> show b
  show (ForSome' q) = "∃" <> show q
  show (Given' (Instance x n ibs ob)) =
    "λ" <> show x
      <> ( if null ibs
             then ""
             else "^" <> show n <> "(" <> intercalate ", " (show <$> ibs) <> ")"
         )
      <> "<"
      <> show ob 

type Quantifier = QuantifierF Name

data AuxTablesF name = AuxTables
  { functionTables :: Map name (Map [Integer] Integer),
    predicateTables :: Map PredicateName (Set [Integer])
  }
  deriving (Eq, Show, Generic)

instance Ord name => Semigroup (AuxTablesF name) where
  (AuxTables ft0 pt0) <> (AuxTables ft1 pt1) = AuxTables (ft0 <> ft1) (pt0 <> pt1)

instance Ord name => Monoid (AuxTablesF name) where
  mempty = AuxTables mempty mempty

type AuxTables = AuxTablesF Name
