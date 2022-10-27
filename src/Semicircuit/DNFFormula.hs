{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}

module Semicircuit.DNFFormula
  ( toDisjunctiveNormalForm,
    fromDisjunctiveNormalForm,
    fromAtom,
    and,
    or,
    atom,
    negAtom,
    top,
    bottom,
  )
where

import Control.Lens ((^.))
import qualified Semicircuit.Types.DNFFormula as DNF
import qualified Semicircuit.Types.QFFormula as QF
import Prelude hiding (and, or, pi)

toDisjunctiveNormalForm :: QF.Formula -> DNF.Formula
toDisjunctiveNormalForm =
  \case
    QF.Equal x y -> atom $ DNF.Equal x y
    QF.LessOrEqual x y -> atom $ DNF.LessOrEqual x y
    QF.Predicate p xs -> atom $ DNF.Predicate p xs
    QF.And p q -> rec p `and` rec q
    QF.Or p q -> rec p `or` rec q
    QF.Implies p q -> rec (QF.Or (QF.Not p) q)
    QF.Iff p q -> rec (QF.Or (QF.And p q) (QF.And (QF.Not p) (QF.Not q)))
    QF.Not (QF.Equal x y) -> negAtom $ DNF.Equal x y
    QF.Not (QF.LessOrEqual x y) -> negAtom $ DNF.LessOrEqual x y
    QF.Not (QF.Predicate p xs) -> negAtom $ DNF.Predicate p xs
    QF.Not (QF.And p q) ->
      rec (QF.Not p) `and` rec (QF.Not q)
    QF.Not (QF.Or p q) ->
      rec (QF.Not p) `and` rec (QF.Not q)
    QF.Not (QF.Implies p q) ->
      rec p `and` rec (QF.Not q)
    QF.Not (QF.Iff p q) ->
      rec (QF.Or (QF.And p (QF.Not q)) (QF.And (QF.Not p) q))
    QF.Not (QF.Not p) -> rec p
    QF.Top -> top
    QF.Bottom -> bottom
    QF.Not QF.Top -> bottom
    QF.Not QF.Bottom -> top
  where
    rec = toDisjunctiveNormalForm

and :: DNF.Formula -> DNF.Formula -> DNF.Formula
and p q =
  DNF.Formula
    [ pi <> qi
      | pi <- p ^. #disjuncts,
        qi <- q ^. #disjuncts
    ]

or :: DNF.Formula -> DNF.Formula -> DNF.Formula
or = (<>)

atom :: DNF.Atom -> DNF.Formula
atom = DNF.Formula . (: []) . DNF.Conjunction . (: []) . DNF.AlmostAtom DNF.Positive

negAtom :: DNF.Atom -> DNF.Formula
negAtom = DNF.Formula . (: []) . DNF.Conjunction . (: []) . DNF.AlmostAtom DNF.Negative

top :: DNF.Formula
top = DNF.Formula [mempty]

bottom :: DNF.Formula
bottom = mempty

fromDisjunctiveNormalForm :: DNF.Formula -> QF.Formula
fromDisjunctiveNormalForm f =
  foldl
    QF.Or
    QF.Bottom
    [ foldl
        QF.And
        QF.Top
        [ case aa ^. #parity of
            DNF.Positive -> fromAtom (aa ^. #atom)
            DNF.Negative -> QF.Not (fromAtom (aa ^. #atom))
          | aa <- c ^. #conjuncts
        ]
      | c <- f ^. #disjuncts
    ]

fromAtom :: DNF.Atom -> QF.Formula
fromAtom =
  \case
    DNF.Equal x y -> QF.Equal x y
    DNF.LessOrEqual x y -> QF.LessOrEqual x y
    DNF.Predicate p xs -> QF.Predicate p xs
