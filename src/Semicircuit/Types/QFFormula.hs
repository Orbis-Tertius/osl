module Semicircuit.Types.QFFormula
  ( Formula (..) ) where


import Data.List.NonEmpty (NonEmpty)

import OSL.Types.Sigma11 (Term, PredicateName)


data Formula =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName (NonEmpty Term)
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
