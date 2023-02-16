{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}

module Halo2.LogicConstraint
  ( toDisjunctiveNormalForm,
    toDisjunctiveNormalForms,
    constantFoldConstraints,
    constantFoldConstraint,
    constantFoldTerm,
  )
where

import Control.Lens ((^.))
import Data.List.Extra (foldl')
import Data.Tuple.Extra (first, second)
import Halo2.Circuit (lessIndicator)
import Halo2.Types.InputExpression (InputExpression (InputExpression))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top), Term (Const, IndLess, Lookup, Max, Plus, Times, Var))
import Halo2.Types.LogicConstraints (LogicConstraints (LogicConstraints))
import Stark.Types.Scalar (one, zero)
import Prelude hiding (and, or)

newtype Disjunction = Disjunction [Conjunction]
  deriving newtype (Semigroup, Monoid)

newtype Conjunction = Conjunction [AlmostAtom]
  deriving newtype (Semigroup, Monoid)

data AlmostAtom = AlmostAtom Parity AtomicLogicConstraint

data Parity = Positive | Negative

toDisjunctiveNormalForms :: LogicConstraints -> LogicConstraints
toDisjunctiveNormalForms (LogicConstraints gates bounds) =
  LogicConstraints (second toDisjunctiveNormalForm <$> gates) bounds

toDisjunctiveNormalForm :: LogicConstraint -> LogicConstraint
toDisjunctiveNormalForm = fromDisjunction . toDisjunction

fromDisjunction :: Disjunction -> LogicConstraint
fromDisjunction (Disjunction disjuncts) =
  foldl'
    Or
    Bottom
    [ foldl'
        And
        Top
        [ case parity of
            Positive -> Atom a
            Negative -> Not (Atom a)
          | AlmostAtom parity a <- conjuncts
        ]
      | Conjunction conjuncts <- disjuncts
    ]

atom :: AtomicLogicConstraint -> Disjunction
atom = Disjunction . (: []) . Conjunction . (: []) . AlmostAtom Positive

negAtom :: AtomicLogicConstraint -> Disjunction
negAtom = Disjunction . (: []) . Conjunction . (: []) . AlmostAtom Negative

and :: Disjunction -> Disjunction -> Disjunction
and (Disjunction ps) (Disjunction qs) =
  Disjunction
    [ p <> q
      | p <- ps,
        q <- qs
    ]

top :: Disjunction
top = Disjunction [mempty]

bottom :: Disjunction
bottom = mempty

toDisjunction :: LogicConstraint -> Disjunction
toDisjunction =
  \case
    Atom a -> atom a
    Not (Atom a) -> negAtom a
    And p q -> rec p `and` rec q
    Not (And p q) -> rec (Not p) <> rec (Not q)
    Or p q -> rec p <> rec q
    Not (Or p q) -> rec (Not p) `and` rec (Not q)
    Iff p q -> rec (Or (And p q) (And (Not p) (Not q)))
    Not (Iff p q) -> (rec p `and` rec (Not q)) <> (rec (Not p) `and` rec q)
    Top -> top
    Not Top -> bottom
    Bottom -> bottom
    Not Bottom -> top
    Not (Not p) -> rec p
  where
    rec = toDisjunction

constantFoldConstraints :: LogicConstraints -> LogicConstraints
constantFoldConstraints lcs =
  LogicConstraints
    (second constantFoldConstraint <$> (lcs ^. #constraints))
    (lcs ^. #bounds)

constantFoldConstraint :: LogicConstraint -> LogicConstraint
constantFoldConstraint =
  \case
    Top -> Top
    Bottom -> Bottom
    Atom (Equals x y) ->
      case (constantFoldTerm x, constantFoldTerm y) of
        (Const i, Const j) | i == j -> Top
        (Const i, Const j) | i /= j -> Bottom
        (x', y') -> Atom (x' `Equals` y')
    Atom (LessThan x y) ->
      case (constantFoldTerm x, constantFoldTerm y) of
        (Const i, Const j) | i < j -> Top
        (Const _, Const _) -> Bottom
        (x', y') -> Atom (x' `LessThan` y')
    Not p ->
      case rec p of
        Top -> Bottom
        Bottom -> Top
        p' -> Not p'
    And p q ->
      case (rec p, rec q) of
        (x', Top) -> x'
        (Top, y') -> y'
        (Bottom, _) -> Bottom
        (_, Bottom) -> Bottom
        (p', q') -> p' `And` q'
    Or p q ->
      case (rec p, rec q) of
        (x', Bottom) -> x'
        (Bottom, y') -> y'
        (Top, _) -> Top
        (_, Top) -> Top
        (p', q') -> p' `Or` q'
    Iff p q ->
      case (rec p, rec q) of
        (x', y') | x' == y' -> Top
        (Top, y') -> y'
        (x', Top) -> x'
        (Bottom, y') -> Not y'
        (x', Bottom) -> Not x'
        (x', y') -> x' `Iff` y'
  where
    rec = constantFoldConstraint

constantFoldTerm :: Term -> Term
constantFoldTerm =
  \case
    Var x -> Var x
    Const i -> Const i
    Plus x y ->
      case (rec x, rec y) of
        (Const i, Const j) -> Const (i + j)
        (Const z, y') | z == zero -> y'
        (x', Const z) | z == zero -> x'
        (x', y') -> x' `Plus` y'
    Times x y ->
      case (rec x, rec y) of
        (Const i, Const j) -> Const (i * j)
        (Const o, y') | o == one -> y'
        (x', Const o) | o == one -> x'
        (x', y') -> x' `Times` y'
    Max x y ->
      case (rec x, rec y) of
        (Const i, Const j) -> Const (i `max` j)
        (x', Const z) | z == zero -> x'
        (Const z, y') | z == zero -> y'
        (x', y') -> x' `Max` y'
    IndLess x y ->
      case (rec x, rec y) of
        (Const i, Const j) -> Const (i `lessIndicator` j)
        (_, Const z) | z == zero -> Const zero
        (x', y') -> x' `IndLess` y'
    Lookup is o ->
      Lookup (first recInput <$> is) o
  where
    rec = constantFoldTerm
    recInput = InputExpression . rec . (^. #getInputExpression)
