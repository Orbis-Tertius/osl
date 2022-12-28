{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLabels #-}

-- This is different from OSL.Types.Sigma11
-- in that the types in this module use explicit
-- variable names rather than de Bruijn indices.
-- This is more convenient for conversion to
-- prenex normal forms.
--
-- You might ask, why not just let the types in
-- OSL.Types.Sigma11 be parameterized by the
-- type of names? The reason is that in
-- OSL.Types.Sigma11, the variable names are implied
-- in quantifiers, whereas in this module, the
-- variable names are given explicitly in quantifiers.

module Semicircuit.Types.Sigma11
  ( Name (Name),
    TermF (..),
    Term,
    var,
    Formula,
    FormulaF (..),
    ExistentialQuantifier,
    ExistentialQuantifierF (..),
    InstanceQuantifier,
    InstanceQuantifierF (..),
    someFirstOrder,
    Bound,
    BoundF (..),
    InputBound,
    InputBoundF (..),
    OutputBound,
    OutputBoundF (..),
    Quantifier,
    QuantifierF (..),
    EvaluationContextF (..),
    EvaluationContext,
  )
where

import Control.Lens ((^.))
import qualified Data.Map as Map
import GHC.Generics (Generic)
import OSL.Sigma11 (HasAddToEvalContext (addToEvalContext), HasIncrementArity (incrementArity))
import OSL.Types.Arity (Arity (Arity))
import OSL.Types.Cardinality (Cardinality (..))
import OSL.Types.Sigma11 (BoundF (..), ExistentialQuantifierF (..), FormulaF (..), InputBoundF (..), InstanceQuantifierF (..), OutputBoundF (..), QuantifierF (..), TermF (Add, App, AppInverse, Const, IndLess, Max, Mul), var)
import OSL.Types.Sigma11.EvaluationContext (EvaluationContextF (EvaluationContext))

data Name = Name {arity :: Arity, sym :: Int}
  deriving (Eq, Ord, Generic)

instance HasIncrementArity Name where
  incrementArity i (Name (Arity j) k) = Name (Arity (i + j)) k

instance HasAddToEvalContext Name where
  addToEvalContext (EvaluationContext c) nm val =
    EvaluationContext (Map.insert nm val c)

instance Show Name where
  show x = "x^" <> show (x ^. #arity) <> "_" <> show (x ^. #sym)

type Term = TermF Name

type Formula = FormulaF Name

type ExistentialQuantifier = ExistentialQuantifierF Name

someFirstOrder :: Name -> Bound -> ExistentialQuantifier
someFirstOrder x b =
  Some x (Cardinality 0) [] (OutputBound b)

type Bound = BoundF Name

type InputBound = InputBoundF Name

type OutputBound = OutputBoundF Name

type Quantifier = QuantifierF Name

type InstanceQuantifier = InstanceQuantifierF Name

type EvaluationContext = EvaluationContextF Name
