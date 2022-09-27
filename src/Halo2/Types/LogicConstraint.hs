{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.LogicConstraint
  ( LogicConstraint (Equals, LessThan, Not, And, Or)
  ) where


import Halo2.Types.Polynomial (Polynomial)


data LogicConstraint =
    Equals Polynomial Polynomial
  | LessThan Polynomial Polynomial
  | Not LogicConstraint
  | And [LogicConstraint]
  | Or [LogicConstraint]
