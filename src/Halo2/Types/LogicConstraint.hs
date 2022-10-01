{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.LogicConstraint
  ( AtomicLogicConstraint (Equals, LessThan)
  , LogicConstraint (Atom, Not, And, Or)
  ) where


import Halo2.Prelude
import Halo2.Types.Polynomial (Polynomial)


data AtomicLogicConstraint =
    Equals Polynomial Polynomial
  | LessThan Polynomial Polynomial
  deriving (Eq, Ord)


data LogicConstraint =
    Atom AtomicLogicConstraint
  | Not LogicConstraint
  | And [LogicConstraint]
  | Or [LogicConstraint]
