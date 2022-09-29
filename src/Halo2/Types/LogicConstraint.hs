{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.LogicConstraint
  ( AtomicLogicConstraint (Equals, LessThan)
  , LogicConstraint (Atom, Not, And, Or)
  ) where


import Halo2.Types.Polynomial (Polynomial)


data AtomicLogicConstraint =
    Equals Polynomial Polynomial
  | LessThan Polynomial Polynomial


data LogicConstraint =
    Atom AtomicLogicConstraint
  | Not LogicConstraint
  | And [LogicConstraint]
  | Or [LogicConstraint]
