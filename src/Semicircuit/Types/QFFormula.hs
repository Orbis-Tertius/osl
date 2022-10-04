module Semicircuit.Types.QFFormula
  ( QFFormula (..) ) where


import Data.List.NonEmpty (NonEmpty)

import OSL.Types.Sigma11 (Term, PredicateName)


data QFFormula =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName (NonEmpty Term)
  | Not QFFormula
  | And QFFormula QFFormula
  | Or QFFormula QFFormula
  | Implies QFFormula QFFormula
  | Iff QFFormula QFFormula
