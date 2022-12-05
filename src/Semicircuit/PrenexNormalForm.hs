{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Semicircuit.PrenexNormalForm
  ( toSuperStrongPrenexNormalForm,
    toStrongPrenexNormalForm,
    toPrenexNormalForm,
  )
where

import Data.Bifunctor (second)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (FromName (FromName), ToName (ToName), prependArguments, prependBounds, substitute, foldConstants)
import Semicircuit.Types.Sigma11 (Bound (FieldMaxBound, TermBound), ExistentialQuantifier (..), Formula (..), InputBound (..), Name, OutputBound (..), Quantifier (..), Term (Add, Const, Max), someFirstOrder, var)

-- Assumes input is in strong prenex normal form.
-- Merges all consecutive same-type quantifiers that can be
-- merged, so, all same-type consecutive quantifiers except
-- for permutation and universal quantifiers are merged.
-- As a result, all instance quantifiers are merged into one,
-- and if there are no permutation quantifiers, then all
-- existential quantifiers are merged into one.
toSuperStrongPrenexNormalForm ::
  ann ->
  [Quantifier] ->
  Formula ->
  Either (ErrorMessage ann) ([Quantifier], Formula)
toSuperStrongPrenexNormalForm = todo

-- Partitions the quantifier sequence into maximal subsequences
-- which are each mergeable into a single quantifier.
groupMergeableQuantifiers ::
  [Quantifier] ->
  [[Quantifier]]
groupMergeableQuantifiers =
  \case
    (Universal x a : qs) ->
      -- Universals are never mergeable, and there is never another
      -- quantifier type after a universal.
      ([Universal x a] : ((:[]) <$> qs))
    (Existential q : Universal x a : qs) ->
      ([Existential q] : [Universal x a] : ((:[]) <$> qs))
    (Existential q : Existential r@(SomeP {}) : qs) ->
      ([Existential q] : [Existential r] : rec qs)
    (Existential q@(SomeP {}) : qs) ->
      ([Existential q] : rec qs)
  where
    rec = groupMergeableQuantifiers

todo :: a
todo = todo

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
          let ab = if a == b then a else foldConstants (a `Max` b')
              p' = if ab == a then p
                   else ((var x `Add` Const 1) `LessOrEqual` a) `And` p
              q' = substitute (FromName y) (ToName x) q
              q'' = if ab == b then q'
                    else ((var x `Add` Const 1) `LessOrEqual` b) `And` q'
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              b' = substitute (FromName y) (ToName x) b
              (pqQs, pq) = mergeQuantifiersConjunctive (pQs, p') (qQs', q'')
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
          let q' = ((var x `Add` Const 1) `LessOrEqual` b) `And` substitute (FromName y) (ToName x) q
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
    ([], p) -> second (And p)

-- Perform prenex normal form conversion on a disjunction
-- of two prenex normal forms, merging existential quantifiers
-- where applicable.
mergeQuantifiersDisjunctive ::
  ([Quantifier], Formula) ->
  ([Quantifier], Formula) ->
  ([Quantifier], Formula)
mergeQuantifiersDisjunctive =
  \case
    (Existential r@(Some x n [] ob@(OutputBound (TermBound obV))) : pQs, p) ->
      \case
        (Existential (Some x' _ [] ob'@(OutputBound (TermBound obV'))) : qQs, q) ->
          let qQs' = substitute (FromName x') (ToName x) <$> qQs
              q' = substitute (FromName x') (ToName x) q
              obV'' = substitute (FromName x') (ToName x) obV'
              obV''' = if ob == ob' then obV
                       else foldConstants (obV `Max` obV'')
              p' = if obV == obV''' then p
                   else ((var x `Add` Const 1) `LessOrEqual` obV) `And` p
              q'' = if obV' == obV''' then q'
                    else ((var x `Add` Const 1) `LessOrEqual` obV'') `And` q'
              (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p') (qQs', q'')
           in (Existential (Some x n [] (OutputBound (TermBound obV'''))) : pqQs, pq)
        (Existential (Some x' _ [] (OutputBound FieldMaxBound)) : qQs, q) ->
          let qQs' = substitute (FromName x') (ToName x) <$> qQs
              q' = substitute (FromName x') (ToName x) q
              p' = ((var x `Add` Const 1) `LessOrEqual` obV) `And` p
              (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p') (qQs', q')
           in (Existential (Some x n [] (OutputBound FieldMaxBound)) : pqQs, pq)
        (qQs, q) ->
          let (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs, q)
           in (Existential r : pqQs, pq)
    (Existential r@(Some x n [] (OutputBound FieldMaxBound)) : pQs, p) ->
      \case
        (Existential (Some x' _ [] (OutputBound (TermBound obV))) : qQs, q) ->
          let qQs' = substitute (FromName x') (ToName x) <$> qQs
              q' =
                ((var x `Add` Const 1) `LessOrEqual` obV)
                  `And` substitute (FromName x') (ToName x) q
              (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs', q')
           in (Existential (Some x n [] (OutputBound FieldMaxBound)) : pqQs, pq)
        (Existential (Some x' _ [] (OutputBound FieldMaxBound)) : qQs, q) ->
          let qQs' = substitute (FromName x') (ToName x) <$> qQs
              q' = substitute (FromName x') (ToName x) q
              (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs', q')
           in (Existential r : pqQs, pq)
        (qQs, q) ->
          let (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs, q)
           in (Existential r : pqQs, pq)
    (Existential r@(Some {}) : pQs, p) -> \(qQs, q) ->
      let (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs, q)
       in (Existential r : pqQs, pq)
    (Existential (SomeP x n ib ob) : pQs, p) ->
      \case
        (Existential (SomeP x' n' ib' ob') : rQs, r) ->
          let ib'' = substitute (FromName x') (ToName x) ib'
              ob'' = substitute (FromName x') (ToName x) ob'
              rQs' = substitute (FromName x') (ToName x) <$> rQs
              r' = substitute (FromName x') (ToName x) r
              (prQs', pr') = mergeQuantifiersDisjunctive (pQs, p) (rQs', r')
              (prQs, pr) = mergeQuantifiersDisjunctive (pQs, p) (rQs, r)
           in if n == n' && ib'' == ib && ob'' == ob
                then (Existential (SomeP x n ib ob) : prQs', pr')
                else (Existential (SomeP x n ib ob) : Existential (SomeP x' n' ib' ob') : prQs, pr)
        (rQs, r) ->
          let (prQs, pr) = mergeQuantifiersDisjunctive (pQs, p) (rQs, r)
           in (Existential (SomeP x n ib ob) : prQs, pr)
    (Universal x a : pQs, p) -> \(qQs, q) ->
      let (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs, q)
       in (Universal x a : pqQs, pq)
    (Instance x n ibs ob : pQs, p) -> \(qQs, q) ->
      let (pqQs, pq) = mergeQuantifiersDisjunctive (pQs, p) (qQs, q)
       in (Instance x n ibs ob : pqQs, pq)
    ([], p) -> second (Or p)

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
