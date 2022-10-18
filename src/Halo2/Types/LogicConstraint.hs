{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.LogicConstraint
  ( AtomicLogicConstraint (Equals, LessThan),
    LogicConstraint (Atom, Not, And, Or, Iff, Top, Bottom),
    atomicConstraintArgs,
  )
where

import Halo2.Prelude
import Halo2.Types.Polynomial (Polynomial)

data AtomicLogicConstraint
  = Equals Polynomial Polynomial
  | LessThan Polynomial Polynomial
  deriving (Eq, Ord)

atomicConstraintArgs :: AtomicLogicConstraint -> (Polynomial, Polynomial)
atomicConstraintArgs =
  \case
    Equals a b -> (a, b)
    LessThan a b -> (a, b)

data LogicConstraint
  = Atom AtomicLogicConstraint
  | Not LogicConstraint
  | And LogicConstraint LogicConstraint
  | Or LogicConstraint LogicConstraint
  | Iff LogicConstraint LogicConstraint
  | Top
  | Bottom
