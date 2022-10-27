{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Semicircuit.Types.DNFFormula
  ( Formula (Formula)
  , Conjunction (Conjunction)
  , AlmostAtom (AlmostAtom)
  , Parity (Positive, Negative)
  , Atom (Equal, LessOrEqual, Predicate)
  ) where


import GHC.Generics (Generic)

import OSL.Types.Sigma11 (PredicateName)
import Semicircuit.Types.Sigma11 (Term)


newtype Formula = Formula { disjuncts :: [Conjunction] }
  deriving stock Generic
  deriving newtype (Semigroup, Monoid)


newtype Conjunction = Conjunction { conjuncts :: [AlmostAtom] }
  deriving stock Generic
  deriving newtype (Semigroup, Monoid)


data AlmostAtom =
  AlmostAtom
  { parity :: Parity
  , atom :: Atom
  }
  deriving Generic


data Parity = Positive | Negative


data Atom =
    Equal Term Term
  | LessOrEqual Term Term
  | Predicate PredicateName [Term]
