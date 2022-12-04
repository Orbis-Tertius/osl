{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LogicConstraint
  ( Term (Var, Const, Plus, Times, Max, IndLess),
    AtomicLogicConstraint (Equals, LessThan),
    LogicConstraint (Atom, Not, And, Or, Iff, Top, Bottom),
    atomicConstraintArgs,
  )
where

import Halo2.Prelude
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Stark.Types.Scalar (Scalar)

data Term
  = Var PolynomialVariable
  | Const Scalar
  | Plus Term Term
  | Times Term Term
  | Max Term Term
  | IndLess Term Term
  deriving (Eq, Ord)

instance Show Term where
  show =
    \case
      Var x -> show x
      Const x -> show x
      Plus x y -> "(" <> show x <> " + " <> show y <> ")"
      Times x y -> "(" <> show x <> " + " <> show y <> ")"
      Max x y -> "(" <> show x <> " max " <> show y <> ")"
      IndLess x y -> "ind<(" <> show x <> ", " <> show y <> ")"

data AtomicLogicConstraint
  = Equals Term Term
  | LessThan Term Term
  deriving (Eq, Ord)

instance Show AtomicLogicConstraint where
  show (Equals x y) =
    "(" <> show x <> " = " <> show y <> ")"
  show (LessThan x y) =
    "(" <> show x <> " < " <> show y <> ")"

atomicConstraintArgs :: AtomicLogicConstraint -> [Term]
atomicConstraintArgs =
  \case
    Equals a b -> [a, b]
    LessThan a b -> [a, b]

data LogicConstraint
  = Atom AtomicLogicConstraint
  | Not LogicConstraint
  | And LogicConstraint LogicConstraint
  | Or LogicConstraint LogicConstraint
  | Iff LogicConstraint LogicConstraint
  | Top
  | Bottom

instance Show LogicConstraint where
  show (Atom x) = show x
  show (Not p) = "!" <> show p
  show (And p q) =
    "(" <> show p <> " & " <> show q <> ")"
  show (Or p q) =
    "(" <> show p <> " | " <> show q <> ")"
  show (Iff p q) =
    "(" <> show p <> " <-> " <> show q <> ")"
  show Top = "⊤"
  show Bottom = "⊥"
