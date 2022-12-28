{-# LANGUAGE DeriveFunctor #-}

module Semicircuit.Types.QFFormula (Formula, FormulaF (..)) where

import Data.List (intercalate)
import OSL.Types.Sigma11 (PredicateName)
import Semicircuit.Types.Sigma11 (Name, TermF)

type Formula = FormulaF Name

data FormulaF name
  = Equal (TermF name) (TermF name)
  | LessOrEqual (TermF name) (TermF name)
  | Predicate PredicateName [TermF name]
  | Not (FormulaF name)
  | And (FormulaF name) (FormulaF name)
  | Or (FormulaF name) (FormulaF name)
  | Implies (FormulaF name) (FormulaF name)
  | Iff (FormulaF name) (FormulaF name)
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
  show (Predicate p qs) =
    show p <> "(" <> intercalate ", " (show <$> qs) <> ")"
  show Top = "⊤"
  show Bottom = "⊥"
