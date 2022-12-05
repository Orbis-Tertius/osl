{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Semicircuit.PrenexNormalForm
  ( toStrongPrenexNormalForm,
    toPrenexNormalForm,
  )
where

import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (prependArguments, prependBounds, substitute, FromName (FromName), ToName (ToName))
import Semicircuit.Types.Sigma11 (Bound (TermBound, FieldMaxBound), ExistentialQuantifier (..), Formula (..), InputBound (..), Name, OutputBound (..), Quantifier (..), someFirstOrder, Term (Add, Const, Max), var)

-- Assumes input is in prenex normal form.
-- Brings all instance quantifiers to the front.
-- Brings all second-order quantifiers next up,
-- along with any first-order existential quantifiers
-- preceding them. Said first-order existential
-- quantifiers become second-order existential
-- quantifiers if there are any universal quantifiers
-- preceding them. Second-order existential quantifiers
-- increase in arity when preceded by universal
-- quantifiers, becoming dependent on those universally
-- quantified values.
toStrongPrenexNormalForm ::
  ann ->
  [Quantifier] ->
  Formula ->
  Either (ErrorMessage ann) ([Quantifier], Formula)
toStrongPrenexNormalForm ann qs f =
  case qs of
    [] -> pure ([], f)
    Existential q : qs' -> do
      (qs'', f') <- rec qs' f
      case qs'' of
        Instance {} : _ ->
          pure (pushExistentialQuantifierDown q qs'', f')
        _ -> pure (Existential q : qs'', f')
    Universal x b : qs' -> do
      (qs'', f') <- rec qs' f
      case qs'' of
        [] -> pure ([Universal x b], f')
        Universal _ _ : _ ->
          pure (Universal x b : qs'', f')
        _ ->
          pushUniversalQuantifiersDown ann [(x, b)] qs'' f'
    Instance x n ibs ob : qs' -> do
      (qs'', f') <- rec qs' f
      pure (Instance x n ibs ob : qs'', f')
  where
    rec = toStrongPrenexNormalForm ann

pushExistentialQuantifierDown ::
  ExistentialQuantifier ->
  [Quantifier] ->
  [Quantifier]
pushExistentialQuantifierDown q =
  \case
    [] -> [Existential q]
    Universal x b : qs ->
      Existential q : Universal x b : qs
    Existential q' : qs ->
      Existential q : Existential q' : qs
    Instance x n ibs obs : qs ->
      Instance x n ibs obs : pushExistentialQuantifierDown q qs

pushUniversalQuantifiersDown ::
  ann ->
  [(Name, Bound)] ->
  [Quantifier] ->
  Formula ->
  Either (ErrorMessage ann) ([Quantifier], Formula)
pushUniversalQuantifiersDown ann us qs f =
  case qs of
    [] -> pure (uncurry Universal <$> us, f)
    Universal x b : qs' ->
      pushUniversalQuantifiersDown ann (us <> [(x, b)]) qs' f
    Existential q : qs' -> do
      (qs'', f') <- pushUniversalQuantifiersDown ann us qs' f
      case q of
        Some g _ _ _ -> do
          let q' = prependBounds (uncurry InputBound <$> us) q
              f'' = prependArguments g (fst <$> us) f'
          pure ([Existential q'] <> qs'', f'')
        SomeP {} ->
          Left . ErrorMessage ann $
            "unsupported: permutation quantifier inside a universal quantifier"
    Instance x n ibs ob : qs' -> do
      (qs'', f') <- pushUniversalQuantifiersDown ann us qs' f
      pure (Instance x n ibs ob : qs'', f')

toPrenexNormalForm ::
  ann ->
  Formula ->
  Either (ErrorMessage ann) ([Quantifier], Formula)
toPrenexNormalForm ann =
  \case
    Equal a b -> pure ([], Equal a b)
    LessOrEqual a b -> pure ([], LessOrEqual a b)
    Predicate p xs -> pure ([], Predicate p xs)
    Top -> pure ([], Top)
    Bottom -> pure ([], Bottom)
    Not p -> do
      (qs, p') <- rec p
      (,Not p') <$> flipQuantifiers ann qs
    And p q -> do
      p' <- rec p
      q' <- rec q
      pure $ mergeQuantifiersConjunctive p' q'
    Or p q -> do
      p' <- rec p
      q' <- rec q
      pure $ mergeQuantifiersDisjunctive p' q'
    Implies p q -> do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      pQs' <- flipQuantifiers ann pQs
      pure $ mergeQuantifiersDisjunctive (pQs', Not p') (qQs, q')
    Iff p q -> do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      case pQs <> qQs of
        [] -> pure ([], Iff p' q')
        _ ->
          Left . ErrorMessage ann $
            "not supported: quantifiers inside <->"
    ForAll x b p -> do
      (pQs, p') <- rec p
      pure (Universal x b : pQs, p')
    ForSome q p -> do
      (pQs, p') <- rec p
      pure (Existential q : pQs, p')
    Given x n ibs ob p -> do
      (pQs, p') <- rec p
      pure (Instance x n ibs ob : pQs, p')
  where
    rec = toPrenexNormalForm ann

todo :: a
todo = todo

-- Performs prenex normal form conversion on a conjunction
-- of two prenex normal forms, merging universal quantifiers
-- where applicable.
mergeQuantifiersConjunctive ::
  ([Quantifier], Formula) ->
  ([Quantifier], Formula) ->
  ([Quantifier], Formula)
mergeQuantifiersConjunctive =
  \case
    (Universal x (TermBound a) : pQs, p) ->
      \case
        (Universal y (TermBound b) : qQs, q) ->
          let p' = ((var x `Add` Const 1) `LessOrEqual` a) `And` p
              q' = ((var x `Add` Const 1) `LessOrEqual` b) `And` (substitute (FromName y) (ToName x) q)
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              b' = substitute (FromName y) (ToName x) b
              (pqQs, pq) = mergeQuantifiersConjunctive (pQs, p') (qQs', q')
              ab = if a == b then a else a `Max` b'
          in (Universal x (TermBound ab) : pqQs, pq)
        (Universal y FieldMaxBound : qQs, q) ->
          let p' = ((var x `Add` Const 1) `LessOrEqual` a) `And` p
              q' = substitute (FromName y) (ToName x) q
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              (pqQs, pq) = mergeQuantifiersConjunctive (pQs, p') (qQs', q')
          in (Universal x FieldMaxBound : pqQs, pq)
        (q : rQs, r) ->
          let (prQs, pr) = mergeQuantifiersConjunctive (pQs, p) (rQs, r)
          in (q : Universal x (TermBound a) : prQs, pr)
        ([], q) -> (Universal x (TermBound a) : pQs, p `And` q)
    (Universal x FieldMaxBound : pQs, p) ->
      \case
        (Universal y FieldMaxBound : qQs, q) ->
          let qQs' = substitute (FromName y) (ToName x) <$> qQs
              (pqQs, pq) = mergeQuantifiersConjunctive (pQs, p) (qQs', q)
          in (Universal x FieldMaxBound : pqQs, pq)
        (Universal y (TermBound b) : qQs, q) ->
          let q' = ((var x `Add` Const 1) `LessOrEqual` b) `And` (substitute (FromName y) (ToName x) q)
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              (pqQs, pq) = mergeQuantifiersConjunctive (pQs, p) (qQs', q')
          in (Universal x FieldMaxBound : pqQs, pq)
        (q : rQs, r) ->
          let (prQs, pr) = mergeQuantifiersConjunctive (pQs, p) (rQs, r)
          in (q : Universal x FieldMaxBound : prQs, pr)
        ([], q) -> (Universal x FieldMaxBound : pQs, p `And` q)
    (Existential q : pQs, p) ->
      \case
        (Universal x a : rQs, r) ->
          let (prQs, pr) = mergeQuantifiersConjunctive (pQs, p) (Universal x a : rQs, r)
          in (Existential q : prQs, pr)
        (r : sQs, s) ->
          let (psQs, ps) = mergeQuantifiersConjunctive (pQs, p) (sQs, s)
          in (r : Existential q : psQs, ps)
        ([], r) -> (Existential q : pQs, p `And` r)
    (Instance x a ibs ob : pQs, p) ->
      \(qQs, q) ->
        let (pqQs, pq) = mergeQuantifiersConjunctive (pQs, p) (qQs, q)
        in (Instance x a ibs ob : pqQs, pq)
    ([], p) -> \(qQs, q) -> (qQs, p `And` q)

-- Perform prenex normal form conversion on a disjunction
-- of two prenex normal forms, merging existential quantifiers
-- where applicable.
mergeQuantifiersDisjunctive ::
  ([Quantifier], Formula) ->
  ([Quantifier], Formula) ->
  ([Quantifier], Formula)
mergeQuantifiersDisjunctive = todo

flipQuantifiers ::
  ann ->
  [Quantifier] ->
  Either (ErrorMessage ann) [Quantifier]
flipQuantifiers ann = mapM (flipQuantifier ann)

flipQuantifier ::
  ann ->
  Quantifier ->
  Either (ErrorMessage ann) Quantifier
flipQuantifier ann =
  \case
    Universal x b ->
      pure (Existential (someFirstOrder x b))
    Existential (Some x _ [] (OutputBound b)) ->
      pure (Universal x b)
    Existential _ ->
      Left . ErrorMessage ann $
        "not supported: second-order quantification in negative position"
    Instance x n ibs ob ->
      pure (Instance x n ibs ob)
