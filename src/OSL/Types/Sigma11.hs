{-# LANGUAGE DeriveGeneric #-}


module OSL.Types.Sigma11
  ( Name (Name)
  , Term (..)
  , Formula (..)
  , ExistentialQuantifier (..)
  ) where


import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty, toList)
import Data.Generics.Labels ()
import GHC.Generics (Generic)

import OSL.Types.Arity (Arity)
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.DeBruijnIndex (DeBruijnIndex)


data Name = Name { arity :: Arity, deBruijnIndex :: DeBruijnIndex }
  deriving (Eq, Ord, Generic)

instance Show Name where
  show (Name a i) = show i <> "^" <> show a


data Term =
    Var Name
  | App Name (NonEmpty Term)
  | Add Term Term
  | Mul Term Term
  | IndLess Term Term
  | Const Integer

instance Show Term where
  show (Var name) = show name
  show (App f xs) =
    show f <> "(" <> intercalate ", " (show <$> toList xs) <> ")"
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
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | ForAll Term Formula
  | Exists ExistentialQuantifier Formula

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
  show (ForAll b p) =
    "(all <" <> show b <> ", " <> show p <> ")"
  show (Exists q p) =
    "(some " <> show q <> ", " <> show p <> ")"


data ExistentialQuantifier =
    ExistsFO Term
  | ExistsSO (Maybe Cardinality) Term (NonEmpty Term)

instance Show ExistentialQuantifier where
  show (ExistsFO b) = "<" <> show b
  show (ExistsSO (Just (Cardinality n)) b bs) =
    "^" <> show n <>
    "<" <> show b <> "("
      <> intercalate ", " (("<" <>) . show <$> toList bs)
      <> ")"
  show (ExistsSO Nothing b bs) =
    "<" <> show b <> "("
      <> intercalate ", " (("<" <>) . show <$> toList bs)
      <> ")"
