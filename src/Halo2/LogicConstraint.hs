{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Halo2.LogicConstraint
  ( toDisjunctiveNormalForm,
    toDisjunctiveNormalForms,
  )
where

import Data.List.Extra (foldl')
import Halo2.Types.LogicConstraint (AtomicLogicConstraint, LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top))
import Halo2.Types.LogicConstraints (LogicConstraints (LogicConstraints))
import Prelude hiding (and, or)

newtype Disjunction = Disjunction [Conjunction]
  deriving newtype (Semigroup, Monoid)

newtype Conjunction = Conjunction [AlmostAtom]
  deriving newtype (Semigroup, Monoid)

data AlmostAtom = AlmostAtom Parity AtomicLogicConstraint

data Parity = Positive | Negative

toDisjunctiveNormalForms :: LogicConstraints -> LogicConstraints
toDisjunctiveNormalForms (LogicConstraints gates bounds) =
  LogicConstraints (toDisjunctiveNormalForm <$> gates) bounds

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
