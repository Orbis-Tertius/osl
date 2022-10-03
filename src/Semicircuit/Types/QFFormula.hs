module Semicircuit.Types.QFFormula
  ( QFFormula (..) ) where


data QFFormula =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName (NonEmpty Term)
  | Not QFFormula
  | And QFFormula QFFormula
  | Or QFFormula QFFormula
  | Implies QFFormula QFFormula
  | Iff QFFormula QFFormula
