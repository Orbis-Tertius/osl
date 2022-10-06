{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}


module OSL.Types.Sigma11
  ( Name (Name)
  , PredicateName (PredicateName)
  , Term (..)
  , var
  , Formula (..)
  , ExistentialQuantifier (..)
  , someFirstOrder
  , InputBound (..)
  , OutputBound (..)
  , Bound (..)
  , AuxTables (..)
  ) where


import Data.List (intercalate)
import Data.Map (Map)
import Data.Set (Set)
import Data.Generics.Labels ()
import GHC.Generics (Generic)

import OSL.Types.Arity (Arity)
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex)


data Name = Name { arity :: Arity, deBruijnIndex :: DeBruijnIndex }
  deriving (Eq, Ord, Generic)

instance Show Name where
  show (Name a i) = show i <> "^" <> show a


data PredicateName = PredicateName { arity :: Arity, deBruijnIndex :: DeBruijnIndex }
  deriving (Eq, Ord, Generic)

instance Show PredicateName where
  show (PredicateName a i) = "P" <> show i <> "^" <> show a


data Term =
    App Name [Term]
  | AppInverse Name Term
  | Add Term Term
  | Mul Term Term
  | IndLess Term Term
  | Const Integer
  deriving Eq

var :: Name -> Term
var x = App x []

instance Show Term where
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
  show (Const x) = show x


data Formula =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName [Term]
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll Bound Formula
  | ForSome ExistentialQuantifier Formula

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
    "(all <" <> show b <> ", " <> show p <> ")"
  show (ForSome q p) =
    "(some " <> show q <> ", " <> show p <> ")"
  show (Predicate p qs) =
     show p <> "(" <> intercalate ", " (show <$> qs) <> ")"


-- In an input bound, de Bruijn indices refer first to the preceding
-- input argument values, with the last argument having the lowest index,
-- and then to the variables in the scope surrounding the quantifier.
newtype InputBound =
  InputBound { unInputBound :: Bound }
  deriving (Eq, Show, Generic)


-- In an output bound, de Bruijn indices refer first to the input
-- argument values, with the last argument having the lowest index,
-- and then to the variables in the scope surrounding the quantifier.
newtype OutputBound =
  OutputBound { unOutputBound :: Bound }
  deriving (Eq, Show, Generic)


data ExistentialQuantifier =
    Some Cardinality [InputBound] OutputBound
  | SomeP Cardinality InputBound OutputBound

someFirstOrder :: Bound -> ExistentialQuantifier
someFirstOrder b =
  Some (Cardinality 0) [] (OutputBound b)

instance Show ExistentialQuantifier where
  show (Some _ [] b) = "<" <> show b
  show (Some (Cardinality n) bs b) =
    "^" <> show n <>
    "<" <> show b <> "("
      <> intercalate ", " (("<" <>) . show <$> bs)
      <> ")"
  show (SomeP (Cardinality n) b0 b1) =
    "^" <> show n <>
    "<" <> show b0 <> "(<" <> show b1 <> ")"


data Bound = TermBound Term | FieldMaxBound
  deriving Eq

instance Show Bound where
  show (TermBound t) = show t
  show FieldMaxBound = show "|F|"


data AuxTables =
  AuxTables
  { functionTables :: Map Name (Map [Integer] Integer)
  , predicateTables :: Map PredicateName (Set [Integer])
  }
  deriving (Eq, Show, Generic)

instance Semigroup AuxTables where
  (AuxTables ft0 pt0) <> (AuxTables ft1 pt1) = AuxTables (ft0 <> ft1) (pt0 <> pt1)

instance Monoid AuxTables where
  mempty = AuxTables mempty mempty
