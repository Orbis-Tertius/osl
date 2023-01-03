{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Semicircuit.PrenexNormalForm
  ( toSuperStrongPrenexNormalForm,
    toStrongPrenexNormalForm,
    witnessToStrongPrenexNormalForm,
    toPrenexNormalForm,
    witnessToPrenexNormalForm,
  )
where

import Cast (intToInteger)
import Control.Applicative (liftA2)
import Control.Lens ((<&>), (^.), _1, _2, _3, _4)
import Control.Monad.State (State, evalState, get, put, replicateM)
import Data.Bifunctor (first, second)
import Data.List (foldl', transpose)
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Die (die)
import OSL.Argument (emptyTree, pairTree)
import OSL.Types.Arity (Arity (Arity))
import OSL.Types.Cardinality (Cardinality)
import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.Sigma11.Argument (Witness (Witness))
import OSL.Types.Sigma11.ValueTree (ValueTree (ValueTree))
import Semicircuit.Gensyms (NextSym (NextSym))
import Semicircuit.Sigma11 (FromName (FromName), HasArity (getArity), HasNames (getNames), ToName (ToName), foldConstants, getInputName, hasFieldMaxBound, prependArguments, prependBounds, substitute)
import Semicircuit.Types.Sigma11 (Bound, BoundF (FieldMaxBound, TermBound), ExistentialQuantifier, ExistentialQuantifierF (..), Formula, FormulaF (..), InputBound, InputBoundF (..), InstanceQuantifierF (Instance), Name (Name), OutputBound, OutputBoundF (..), Quantifier, QuantifierF (..), Term, TermF (Add, Const, IndLess, Max, Mul), someFirstOrder, var)

-- Assumes input is in strong prenex normal form.
-- Merges all consecutive same-type quantifiers that can be
-- merged, so, all same-type consecutive quantifiers except
-- for permutation and universal quantifiers are merged.
-- As a result, all instance quantifiers are merged into one,
-- and if there are no permutation quantifiers, then all
-- existential quantifiers are merged into one.
toSuperStrongPrenexNormalForm ::
  [Quantifier] ->
  Formula ->
  ([Quantifier], Formula)
toSuperStrongPrenexNormalForm qs f =
  let (qs', substitutions) =
        unzip . flip evalState nextSym $
          mapM mergeQuantifiers (groupMergeableQuantifiers qs)
   in (qs', foldl' (.) id substitutions f)
  where
    nextSym :: NextSym
    nextSym = NextSym (1 + foldl' max 0 ((^. #sym) <$> Set.toList (mconcat (getNames <$> qs) <> getNames f)))

-- Assumes the quantifier sequence is mergeable into a single
-- quantifier. Returns the merged quantifier and the substitution
-- function to apply to replace applications of the non-merged
-- quantified variables with applications of the merged quantified
-- variable.
mergeQuantifiers ::
  [Quantifier] ->
  State NextSym (Quantifier, Formula -> Formula)
mergeQuantifiers [q] = pure (q, id)
mergeQuantifiers qs = do
  let (qs', padSubst) = padToSameArity qs
  (q, mergeSubst) <- mergePaddedQuantifiers qs'
  pure (q, mergeSubst . padSubst)

-- Assumes the quantifier sequence is mergeable into a single
-- quantifier. Returns the same quantifier sequence but with all
-- quantified variables padded with extra arguments as needed to
-- make them all the same arity. Also returns their common arity
-- and a substitution to apply to pad all function applications with
-- zeroes as needed to be consistent.
padToSameArity ::
  [Quantifier] ->
  ([Quantifier], Formula -> Formula)
padToSameArity qs =
  let arity = foldl' max 0 (getArity <$> qs)
      (qs', subs) = unzip (padToArity arity <$> qs)
   in (qs', foldl' (.) id subs)

-- Returns the given quantifier padded with extra arguments as
-- needed to bring it to the given arity. Assumes that this can
-- be done. Also returns a substitution to apply to pad all
-- function applications with zeroes as needed to be consistent.
padToArity ::
  Arity ->
  Quantifier ->
  (Quantifier, Formula -> Formula)
padToArity arity =
  \case
    ForAll' {} -> die "padToArity: saw a universal quantifier (this is a compiler bug)"
    ForSome' (SomeP {}) -> die "padToArity: saw a permutation quantifier (this is a compiler bug)"
    ForSome' (Some x n ibs ob) ->
      let d = (arity ^. #unArity) - length ibs
          x' = Name arity (x ^. #sym)
       in ( ForSome' $ Some x' n (replicate d (UnnamedInputBound (TermBound (Const 1))) <> ibs) ob,
            prependArguments x (replicate d (Const 0))
          )
    Given' (Instance x n ibs ob) ->
      let d = (arity ^. #unArity) - length ibs
          x' = Name arity (x ^. #sym)
       in ( Given' (Instance x' n (replicate d (UnnamedInputBound (TermBound (Const 1))) <> ibs) ob),
            prependArguments x (replicate d (Const 0))
          )

-- Assumes the quantifier sequence is mergeable into a single
-- quantifier, and the quantifiers in the sequence all have the
-- given arity. Returns the merged quantifier and the
-- substitution to replace all applications of the non-merged
-- quantified variables with applications of the merged quantified
-- variable.
mergePaddedQuantifiers ::
  [Quantifier] ->
  State NextSym (Quantifier, Formula -> Formula)
mergePaddedQuantifiers =
  \case
    [] -> die "mergePaddedQuantifiers: empty quantifier list (this is a compiler bug)"
    qs@(ForSome' _ : _) ->
      mergePaddedExistentialQuantifiers qs
    qs@(Given' {} : _) ->
      mergePaddedInstanceQuantifiers qs
    ForAll' {} : _ ->
      die "mergePaddedQuantifiers: saw a universal quantifier (this is a compiler bug)"

mergePaddedExistentialQuantifiers ::
  [Quantifier] ->
  State NextSym (Quantifier, Formula -> Formula)
mergePaddedExistentialQuantifiers qs =
  first sigToExistential <$> mergePaddedQuantifierSigs (quantifierSig <$> qs)

mergePaddedInstanceQuantifiers ::
  [Quantifier] ->
  State NextSym (Quantifier, Formula -> Formula)
mergePaddedInstanceQuantifiers qs =
  first sigToInstance <$> mergePaddedQuantifierSigs (quantifierSig <$> qs)

quantifierSig :: Quantifier -> (Name, Cardinality, [InputBound], OutputBound)
quantifierSig =
  \case
    ForSome' (Some x n ibs ob) -> (x, n, ibs, ob)
    ForSome' (SomeP {}) -> die "quantifierSig: saw a permutation quantifier (this is a compiler bug)"
    Given' (Instance x n ibs ob) -> (x, n, ibs, ob)
    ForAll' {} -> die "quantifierSig: saw a universal quantifier (this is a compiler bug)"

sigToExistential :: (Name, Cardinality, [InputBound], OutputBound) -> Quantifier
sigToExistential (x, n, ibs, ob) = ForSome' (Some x n ibs ob)

sigToInstance :: (Name, Cardinality, [InputBound], OutputBound) -> Quantifier
sigToInstance (x, n, ibs, ob) = Given' (Instance x n ibs ob)

mergePaddedQuantifierSigs ::
  [(Name, Cardinality, [InputBound], OutputBound)] ->
  State NextSym ((Name, Cardinality, [InputBound], OutputBound), Formula -> Formula)
mergePaddedQuantifierSigs [] = die "mergePaddedQuantifierSigs: no signatures provided (this is a compiler bug)"
mergePaddedQuantifierSigs sigs@((_, _, ibs, _) : _) = do
  h <- Name (Arity (length ibs + 1)) <$> getNextSym
  (,) <$> (uncurry (h,cardinality,,) <$> mergedBounds)
    <*> pure (substitutions h)
  where
    cardinality :: Cardinality
    cardinality = foldl' (+) 0 $ (^. _2) <$> sigs

    quantifierNames :: [Name]
    quantifierNames = sigs <&> (^. _1)

    mergedBounds :: State NextSym ([InputBound], OutputBound)
    mergedBounds = do
      tagName <- Name 0 <$> getNextSym
      inputNames <- replicateM (length ibs) (Name 0 <$> getNextSym)
      let tagBound :: InputBound
          tagBound = NamedInputBound tagName (TermBound (Const (intToInteger (length sigs))))

          tagIndicators :: [Term] -- one per input sig
          tagIndicators =
            [ (var tagName `Add` Const (intToInteger (negate i))) `IndLess` Const 1
              | i <- [0 .. length sigs - 1]
            ]

          inputNameSubstitutions :: [Term -> Term] -- one per input sig
          inputNameSubstitutions =
            [ foldl'
                (.)
                id
                [ substitute (FromName fromName) (ToName toName)
                  | (toName, fromName) <-
                      catMaybes $
                        zipWith
                          (liftA2 (,))
                          (pure <$> inputNames)
                          (getInputName <$> is)
                ]
              | is <- inputBounds
            ]

          boundTerm :: Bound -> Term
          boundTerm b =
            case b of
              TermBound x -> x
              FieldMaxBound -> die "mergePaddedQuantifierSigs: saw an |F| bound (this is a compiler bug)"

          inputBounds :: [[InputBound]] -- one list per input sig
          inputBounds = sigs <&> (^. _3)

          inputBoundTerms :: [[Term]] -- one list per input sig
          inputBoundTerms = fmap (boundTerm . (^. #bound)) <$> inputBounds

          mergedInputBounds :: [InputBound]
          mergedInputBounds =
            [ NamedInputBound xi . TermBound $
                foldl'
                  Add
                  (Const 0)
                  [ tagIndicator `Mul` sub bi
                    | (tagIndicator, sub, bi) <- zip3 tagIndicators inputNameSubstitutions bis
                  ]
              | (xi, bis) <- zip inputNames (transpose inputBoundTerms)
            ]

          outputBoundTerms :: [Term] -- one per input sig
          outputBoundTerms = sigs <&> (boundTerm . (^. _4 . #unOutputBound))

          mergedOutputBound :: OutputBound
          mergedOutputBound =
            OutputBound . TermBound $
              foldl'
                Add
                (Const 0)
                [ tagIndicator `Mul` sub bi
                  | (tagIndicator, sub, bi) <- zip3 tagIndicators inputNameSubstitutions outputBoundTerms
                ]

      pure (tagBound : mergedInputBounds, mergedOutputBound)

    substitutions :: Name -> Formula -> Formula
    substitutions h = functionNameSubstitutions h . tagPrependingSubstitutions

    functionNameSubstitutions :: Name -> Formula -> Formula
    functionNameSubstitutions h =
      foldl'
        (.)
        id
        [ substitute (FromName f') (ToName h)
          | f <- quantifierNames,
            let f' = Name (f ^. #arity + 1) (f ^. #sym)
        ]

    tagPrependingSubstitutions :: Formula -> Formula
    tagPrependingSubstitutions =
      foldl'
        (.)
        id
        [ prependArguments f [Const i]
          | (i, f) <- zip [0 ..] quantifierNames
        ]

getNextSym :: State NextSym Int
getNextSym = do
  NextSym next <- get
  put (NextSym (next + 1))
  pure next

-- Assumes the quantifier sequence is in strong prenex normal form.
-- Partitions the quantifier sequence into maximal subsequences
-- which are each mergeable into a single quantifier.
groupMergeableQuantifiers ::
  [Quantifier] ->
  [[Quantifier]]
groupMergeableQuantifiers =
  \case
    (ForAll' x a : qs) ->
      -- Universals are never mergeable, and there is never another
      -- quantifier type after a universal.
      ([ForAll' x a] : ((: []) <$> qs))
    (ForSome' q : ForAll' x a : qs) ->
      ([ForSome' q] : [ForAll' x a] : ((: []) <$> qs))
    (ForSome' q : ForSome' r@(SomeP {}) : qs) ->
      ([ForSome' q] : [ForSome' r] : rec qs)
    (ForSome' q@(SomeP {}) : qs) ->
      ([ForSome' q] : rec qs)
    (ForSome' q@(Some x _ _ _) : ForSome' r : qs) ->
      case rec (ForSome' r : qs) of
        (rs : qss) ->
          if x `Set.member` mconcat (getNames <$> rs)
            || hasFieldMaxBound (ForSome' q)
            || any hasFieldMaxBound rs
            then -- Not mergeable; since names are not reused, the name x
            -- being present in r indicates that a bound of r depends on x.
            -- Also, for now, quantifiers containing field max bounds are
            -- not mergeable.
              [ForSome' q] : rs : qss
            else -- mergeable
              (ForSome' q : rs) : qss
        [] -> die "groupMergeableQuantifiers: empty result for non-empty recursion (this is a compiler bug)"
    (ForSome' _ : Given' {} : _) ->
      die "groupMergeableQuantifiers: input is not in strong prenex normal form (this is a compiler bug)"
    (q@(Given' {}) : ForSome' r : qs) ->
      [q] : rec (ForSome' r : qs)
    (q@(Given' {}) : r@(ForAll' {}) : qs) ->
      [q] : rec (r : qs)
    (q@(Given' (Instance x _ _ _)) : r@(Given' {}) : qs) ->
      case rec (r : qs) of
        (rs : qss) ->
          if x `Set.member` mconcat (getNames <$> rs)
            then -- not mergeable
              [q] : rs : qss
            else -- mergeable
              (q : rs) : qss
        [] -> die "groupMergeableQuantifiers: empty result for non-empty recursion (this is a compiler bug)"
    [q] -> [[q]]
    [] -> []
  where
    rec = groupMergeableQuantifiers

-- Assumes input is in prenex normal form.
-- Brings all instance quantifiers to the front.
-- Brings all existential quantifiers next up.
-- First-order existential
-- quantifiers become second-order existential
-- quantifiers if there are any universal quantifiers
-- preceding them. Second-order existential quantifiers
-- increase in arity when preceded by universal
-- quantifiers, becoming dependent on those universally
-- quantified values.
-- In the result, quantifiers are all at the front,
-- and they consist of a string of instance quantifiers,
-- followed by a string of existential quantifiers,
-- followed by a string of universal quantifiers.
toStrongPrenexNormalForm ::
  ann ->
  [Quantifier] ->
  Formula ->
  Either (ErrorMessage ann) ([Quantifier], Formula)
toStrongPrenexNormalForm ann qs f =
  case qs of
    [] -> pure ([], f)
    ForSome' q : qs' -> do
      (qs'', f') <- rec qs' f
      case qs'' of
        Given' {} : _ ->
          pure (pushExistentialQuantifierDown q qs'', f')
        _ -> pure (ForSome' q : qs'', f')
    ForAll' x b : qs' -> do
      (qs'', f') <- rec qs' f
      case qs'' of
        [] -> pure ([ForAll' x b], f')
        ForAll' _ _ : _ ->
          pure (ForAll' x b : qs'', f')
        _ ->
          pushUniversalQuantifiersDown ann [(x, b)] qs'' f'
    Given' (Instance x n ibs ob) : qs' -> do
      (qs'', f') <- rec qs' f
      pure (Given' (Instance x n ibs ob) : qs'', f')
  where
    rec = toStrongPrenexNormalForm ann

witnessToStrongPrenexNormalForm ::
  ann ->
  [Quantifier] ->
  Witness ->
  Either (ErrorMessage ann) Witness
witnessToStrongPrenexNormalForm ann qs w =
  case qs of
    [] -> pure w
    ForSome' _ : qs' ->
      case w of
        Witness (ValueTree (Just f) [w']) -> do
          Witness . ValueTree (Just f) . (:[]) . (^. #unWitness)
            <$> rec qs' (Witness w')
        _ -> Left (ErrorMessage ann "expected an existential-shaped witness")
    ForAll' x b : qs' ->
      pushUniversalQuantifiersDownWitness ann [(x, b)] qs' w
    Given' _ : qs' -> rec qs' w
  where
    rec = witnessToStrongPrenexNormalForm ann

pushExistentialQuantifierDown ::
  ExistentialQuantifier ->
  [Quantifier] ->
  [Quantifier]
pushExistentialQuantifierDown q =
  \case
    [] -> [ForSome' q]
    ForAll' x b : qs ->
      ForSome' q : ForAll' x b : qs
    ForSome' q' : qs ->
      ForSome' q : ForSome' q' : qs
    Given' (Instance x n ibs obs) : qs ->
      Given' (Instance x n ibs obs) : pushExistentialQuantifierDown q qs

pushUniversalQuantifiersDown ::
  ann ->
  [(Name, Bound)] ->
  [Quantifier] ->
  Formula ->
  Either (ErrorMessage ann) ([Quantifier], Formula)
pushUniversalQuantifiersDown ann us qs f =
  case qs of
    [] -> pure (uncurry ForAll' <$> us, f)
    ForAll' x b : qs' ->
      pushUniversalQuantifiersDown ann (us <> [(x, b)]) qs' f
    ForSome' q : qs' -> do
      (qs'', f') <- pushUniversalQuantifiersDown ann us qs' f
      case q of
        Some g n _ _ -> do
          let q' = prependBounds n (uncurry NamedInputBound <$> us) q
              f'' = prependArguments g (var . fst <$> us) f'
          pure ([ForSome' q'] <> qs'', f'')
        SomeP {} ->
          Left . ErrorMessage ann $
            "unsupported: permutation quantifier inside a universal quantifier"
    Given' (Instance x n ibs ob) : qs' -> do
      (qs'', f') <- pushUniversalQuantifiersDown ann us qs' f
      pure (Given' (Instance x n ibs ob) : qs'', f')

pushUniversalQuantifiersDownWitness ::
  ann ->
  [(Name, Bound)] ->
  [Quantifier] ->
  Witness ->
  Either (ErrorMessage ann) Witness
pushUniversalQuantifiersDownWitness ann us qs (Witness w) =
  case qs of
    [] -> pure (Witness w)
    ForAll' x b : qs' ->
      rec (us <> [(x,b)]) qs' (Witness w)
    ForSome' q : qs' -> todo q qs'
    Given' _ : _ ->
      Left (ErrorMessage ann "pushUniversalQuantifiersDownWitness: encountered a lambda but expected lambdas to be stripped (this is a compiler bug)")
  where
    rec = pushUniversalQuantifiersDownWitness ann

todo :: a
todo = todo

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
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      pure (pQs <> qQs, p' `Or` q')
    Implies p q -> do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      pQs' <- flipQuantifiers ann pQs
      pure (pQs' <> qQs, p' `Implies` q')
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
      pure (ForAll' x b : pQs, p')
    ForSome q p -> do
      (pQs, p') <- rec p
      pure (ForSome' q : pQs, p')
    Given x n ibs ob p -> do
      (pQs, p') <- rec p
      pure (Given' (Instance x n ibs ob) : pQs, p')
  where
    rec = toPrenexNormalForm ann

-- Performs the operation analogous to toPrenexNormalForm,
-- on a witness.
witnessToPrenexNormalForm ::
  Formula ->
  Witness ->
  Either (ErrorMessage ()) Witness
witnessToPrenexNormalForm =
  curry $
    \case
      (Equal {}, w) -> pure w
      (LessOrEqual {}, w) -> pure w
      (Predicate {}, w) -> pure w
      (Not (Equal {}), w) -> pure w
      (Not (LessOrEqual {}), w) -> pure w
      (Not (Predicate {}), w) -> pure w
      (And p q, Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, p') <- toPrenexNormalForm () p
        (qQs, q') <- toPrenexNormalForm () q
        w0' <- rec p (Witness w0)
        w1' <- rec q (Witness w1)
        mergeWitnessesConjunctive (pQs, p', w0') (qQs, q', w1')
      (And {}, _) -> Left (ErrorMessage () "expected a conjunction shaped witness")
      (Not (Or p q), Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, p') <- toPrenexNormalForm () (Not p)
        (qQs, q') <- toPrenexNormalForm () (Not q)
        w0' <- rec p (Witness w0)
        w1' <- rec q (Witness w1)
        mergeWitnessesConjunctive (pQs, p', w0') (qQs, q', w1')
      (Not (Or {}), _) -> Left (ErrorMessage () "expected a negated disjunction shaped witness")
      (Or p q, Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, p') <- toPrenexNormalForm () p
        (qQs, q') <- toPrenexNormalForm () q
        w0' <- rec p (Witness w0)
        w1' <- rec q (Witness w1)
        mergeWitnessesDisjunctive (pQs, p', w0') (qQs, q', w1')
      (Or {}, _) -> Left (ErrorMessage () "expected a disjunction shaped witness")
      (Not (And p q), Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, p') <- toPrenexNormalForm () (Not p)
        (qQs, q') <- toPrenexNormalForm () (Not q)
        w0' <- rec p (Witness w0)
        w1' <- rec q (Witness w1)
        mergeWitnessesDisjunctive (pQs, p', w0') (qQs, q', w1')
      (Not (And {}), _) -> Left (ErrorMessage () "expected a negated conjunction shaped witness")
      (Implies p q, Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, p') <- toPrenexNormalForm () (Not p)
        (qQs, q') <- toPrenexNormalForm () q
        w0' <- rec p (Witness w0)
        w1' <- rec q (Witness w1)
        mergeWitnessesDisjunctive (pQs, p', w0') (qQs, q', w1')
      (Implies {}, _) -> Left (ErrorMessage () "expected an implication shaped witness")
      (Not (Implies p q), Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, p') <- toPrenexNormalForm () p
        (qQs, q') <- toPrenexNormalForm () (Not q)
        w0' <- rec p (Witness w0)
        w1' <- rec q (Witness w1)
        mergeWitnessesConjunctive (pQs, p', w0') (qQs, q', w1')
      (Not (Implies {}), _) -> Left (ErrorMessage () "expected a negated implication shaped witness")
      (Iff p q, Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, _) <- toPrenexNormalForm () p
        (qQs, _) <- toPrenexNormalForm () q
        case (pQs, qQs) of
          ([], []) -> do
            w0' <- rec p (Witness w0)
            w1' <- rec q (Witness w1)
            pure (Witness (pairTree (w0' ^. #unWitness) (w1' ^. #unWitness)))
          _ -> Left (ErrorMessage () "unsupported: quantifiers inside biconditional")
      (Iff {}, _) -> Left (ErrorMessage () "expected a biconditional shaped witness")
      (Not (Iff p q), Witness (ValueTree Nothing [w0, w1])) -> do
        (pQs, _) <- toPrenexNormalForm () p
        (qQs, _) <- toPrenexNormalForm () q
        case (pQs, qQs) of
          ([], []) -> do
            w0' <- rec p (Witness w0)
            w1' <- rec q (Witness w1)
            pure (Witness (pairTree (w0' ^. #unWitness) (w1' ^. #unWitness)))
          _ -> Left (ErrorMessage () "unsupported: quantifiers inside biconditional")
      (Not (Iff {}), _) -> Left (ErrorMessage () "expected a negated biconditional shaped witness")
      (Not (Not p), w) -> rec p w
      (ForAll _ _ p, Witness (ValueTree Nothing ws)) ->
        Witness . ValueTree Nothing
          <$> mapM (fmap (^. #unWitness) . rec p . Witness) ws
      (ForAll {}, _) -> Left (ErrorMessage () "expected a universal shaped witness")
      (Not (ForAll _ _ p), Witness (ValueTree (Just f) [w])) ->
        Witness . ValueTree (Just f) . (: []) . (^. #unWitness) <$> rec (Not p) (Witness w)
      (Not (ForAll {}), _) -> Left (ErrorMessage () "expected a negated universal shaped witness")
      (ForSome _ p, Witness (ValueTree (Just f) [w])) ->
        Witness . ValueTree (Just f) . (: []) . (^. #unWitness) <$> rec p (Witness w)
      (ForSome {}, _) -> Left (ErrorMessage () "expected an existential shaped witness")
      (Not (ForSome _ p), Witness (ValueTree Nothing ws)) ->
        Witness . ValueTree Nothing
          <$> mapM (fmap (^. #unWitness) . rec (Not p) . Witness) ws
      (Not (ForSome {}), _) -> Left (ErrorMessage () "expected a negated existential shaped witness")
      (Given _ _ _ _ p, w) -> rec p w
      (Not (Given {}), _) -> Left (ErrorMessage () "unsupported: instance quantifier in negative position")
      (Not Top, w) -> pure w
      (Top, w) -> pure w
      (Not Bottom, w) -> pure w
      (Bottom, w) -> pure w
  where
    rec = witnessToPrenexNormalForm

-- Performs prenex normal form conversion on a conjunction
-- of two prenex normal forms, merging universal quantifiers
-- where applicable.
mergeQuantifiersConjunctive ::
  ([Quantifier], Formula) ->
  ([Quantifier], Formula) ->
  ([Quantifier], Formula)
mergeQuantifiersConjunctive =
  \case
    (ForAll' x (TermBound a) : pQs, p) ->
      \case
        (ForAll' y (TermBound b) : qQs, q) ->
          let ab = if a == b then a else foldConstants (a `Max` b')
              p' =
                if ab == a
                  then p
                  else ((var x `Add` Const 1) `LessOrEqual` a) `Implies` p
              q' = substitute (FromName y) (ToName x) q
              q'' =
                if ab == b
                  then q'
                  else ((var x `Add` Const 1) `LessOrEqual` b) `Implies` q'
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              b' = substitute (FromName y) (ToName x) b
              (pqQs, pq) = rec (pQs, p') (qQs', q'')
           in (ForAll' x (TermBound ab) : pqQs, pq)
        (ForAll' y FieldMaxBound : qQs, q) ->
          let p' = ((var x `Add` Const 1) `LessOrEqual` a) `Implies` p
              q' = substitute (FromName y) (ToName x) q
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              (pqQs, pq) = rec (pQs, p') (qQs', q')
           in (ForAll' x FieldMaxBound : pqQs, pq)
        (q : rQs, r) ->
          let (prQs, pr) = rec (pQs, p) (rQs, r)
           in (q : ForAll' x (TermBound a) : prQs, pr)
        ([], q) -> (ForAll' x (TermBound a) : pQs, p `Implies` q)
    (ForAll' x FieldMaxBound : pQs, p) ->
      \case
        (ForAll' y FieldMaxBound : qQs, q) ->
          let qQs' = substitute (FromName y) (ToName x) <$> qQs
              (pqQs, pq) = rec (pQs, p) (qQs', q)
           in (ForAll' x FieldMaxBound : pqQs, pq)
        (ForAll' y (TermBound b) : qQs, q) ->
          let q' = ((var x `Add` Const 1) `LessOrEqual` b) `Implies` substitute (FromName y) (ToName x) q
              qQs' = substitute (FromName y) (ToName x) <$> qQs
              (pqQs, pq) = rec (pQs, p) (qQs', q')
           in (ForAll' x FieldMaxBound : pqQs, pq)
        (q : rQs, r) ->
          let (prQs, pr) = rec (pQs, p) (rQs, r)
           in (q : ForAll' x FieldMaxBound : prQs, pr)
        ([], q) -> (ForAll' x FieldMaxBound : pQs, p `And` q)
    (ForSome' q : pQs, p) ->
      \case
        (ForAll' x a : rQs, r) ->
          let (prQs, pr) = rec (pQs, p) (ForAll' x a : rQs, r)
           in (ForSome' q : prQs, pr)
        (r : sQs, s) ->
          let (psQs, ps) = rec (pQs, p) (sQs, s)
           in (ForSome' q : r : psQs, ps)
        ([], r) -> (ForSome' q : pQs, p `And` r)
    (Given' (Instance x a ibs ob) : pQs, p) ->
      \(qQs, q) ->
        let (pqQs, pq) = rec (pQs, p) (qQs, q)
         in (Given' (Instance x a ibs ob) : pqQs, pq)
    ([], p) -> second (And p)
  where
    rec = mergeQuantifiersConjunctive

-- mergeWitnessesDisjunctive does the corresponding operation on witnesses
-- to the disjunctive cases of prenex normal form conversion.
--
-- In disjunctive cases of prenex normal form conversion, we just put all the
-- left-hand quantifiers to the left of all the right-hand quantifiers.
-- This is not the most efficient approach, presumably, and we should put
-- some thought into how to better optimize this stage of the pipeline.
mergeWitnessesDisjunctive ::
  ([Quantifier], Formula, Witness) ->
  ([Quantifier], Formula, Witness) ->
  Either (ErrorMessage ()) Witness
mergeWitnessesDisjunctive =
  curry $
    \case
      (([], _, Witness w0), ([], _, Witness w1)) ->
        pure (Witness (pairTree w0 w1))
      (([], p, w0), (ForSome' {} : qs, q, Witness (ValueTree (Just f) [w1]))) ->
        Witness . ValueTree (Just f) . (: []) . (^. #unWitness)
          <$> rec ([], p, w0) (qs, q, Witness w1)
      (([], _, _), (ForSome' {} : _, _, _)) ->
        Left (ErrorMessage () "expected an existential shaped witness on the right")
      (([], p, w0), (ForAll' {} : qs, q, Witness (ValueTree Nothing w1s))) ->
        Witness . ValueTree Nothing
          <$> sequence
            [rec ([], p, w0) (qs, q, Witness w1) <&> (^. #unWitness) | w1 <- w1s]
      (([], _, _), (ForAll' {} : _, _, _)) ->
        Left (ErrorMessage () "expected a universal shaped witness on the right")
      (([], p, w0), (Given' {} : qs, q, w1)) ->
        rec ([], p, w0) (qs, q, w1)
      ((ForAll' {} : qs0, p, Witness (ValueTree Nothing w0s)), (qs1, q, w1)) ->
        Witness . ValueTree Nothing
          <$> sequence
            [rec (qs0, p, Witness w0) (qs1, q, w1) <&> (^. #unWitness) | w0 <- w0s]
      ((ForAll' {} : _, _, _), _) -> Left (ErrorMessage () "expected a universal shaped witness on the left")
      ((ForSome' {} : qs0, p, Witness (ValueTree (Just f) [w0])), (qs1, q, w1)) ->
        Witness . ValueTree (Just f) . (: []) . (^. #unWitness)
          <$> rec (qs0, p, Witness w0) (qs1, q, w1)
      ((ForSome' {} : _, _, _), _) -> Left (ErrorMessage () "expected an existential shaped witness on the left")
      ((Given' {} : qs0, p, w0), (qs1, q, w1)) ->
        rec (qs0, p, w0) (qs1, q, w1)
  where
    rec = mergeWitnessesDisjunctive

-- Performs the analogous operation to mergeQuantifiersConjunctive,
-- but on the witness. Assumes the provided formulas are quantifier free.
mergeWitnessesConjunctive ::
  ([Quantifier], Formula, Witness) ->
  ([Quantifier], Formula, Witness) ->
  Either (ErrorMessage ()) Witness
mergeWitnessesConjunctive =
  curry $
    \case
      (([], _, Witness w0), ([], _, Witness w1)) ->
        pure (Witness (pairTree w0 w1))
      ( (ForAll' {} : qs0, p, Witness (ValueTree Nothing w0s)),
        (ForAll' {} : qs1, q, Witness (ValueTree Nothing w1s))
        ) ->
          Witness . ValueTree Nothing
            <$> sequence
              [ rec (qs0, p, Witness w0) (qs1, q, Witness w1) <&> (^. #unWitness)
                | (w0, w1) <- zipAndPad emptyTree w0s emptyTree w1s
              ]
      ((ForAll' {} : _, _, _), (ForAll' {} : _, _, _)) ->
        Left (ErrorMessage () "expected two universal quantifier shaped witnesses but at least one of two was not")
      ( (ForSome' {} : qs0, p, Witness (ValueTree (Just f) [w0])),
        (qs1@(ForAll' {} : _), q, Witness (ValueTree Nothing w1))
        ) ->
          Witness . ValueTree (Just f) . (: []) . (^. #unWitness)
            <$> rec (qs0, p, Witness w0) (qs1, q, Witness (ValueTree Nothing w1))
      ((ForSome' {} : _, _, _), (ForAll' {} : _, _, _)) ->
        Left (ErrorMessage () "expected an existential shaped witness and a universal shaped witness")
      ( (qs0@(ForAll' {} : _), p, Witness (ValueTree Nothing w0)),
        (ForSome' {} : qs1, q, Witness (ValueTree (Just f) [w1]))
        ) ->
          Witness . ValueTree (Just f) . (: []) . (^. #unWitness)
            <$> rec (qs0, p, Witness (ValueTree Nothing w0)) (qs1, q, Witness w1)
      ((ForAll' {} : _, _, _), (ForSome' {} : _, _, _)) ->
        Left (ErrorMessage () "expected a universal shaped witness and an existential witness")
      ( (ForSome' {} : qs0, p, Witness (ValueTree (Just f) [w0])),
        (ForSome' {} : qs1, q, Witness (ValueTree (Just g) [w1]))
        ) ->
          Witness . ValueTree (Just f) . (: []) . ValueTree (Just g) . (: []) . (^. #unWitness)
            <$> rec (qs0, p, Witness w0) (qs1, q, Witness w1)
      ((ForSome' {} : _, _, _), (ForSome' {} : _, _, _)) ->
        Left (ErrorMessage () "expected two existential shaped witnesses but at least one was not")
      ((Given' {} : qs0, p, w0), (qs1, q, w1)) ->
        rec (qs0, p, w0) (qs1, q, w1)
      ((qs0, p, w0), (Given' {} : qs1, q, w1)) ->
        rec (qs0, p, w0) (qs1, q, w1)
      ((ForAll' {} : qs, p, Witness (ValueTree Nothing w0s)), ([], q, w1)) ->
        Witness . ValueTree Nothing
          <$> sequence
            [ rec (qs, p, w0) ([], q, w1) <&> (^. #unWitness)
              | w0 <- Witness <$> w0s
            ]
      ((ForAll' {} : _, _, _), ([], _, _)) ->
        Left (ErrorMessage () "expected a universal quantifier shaped witness on the left")
      (([], p, w0), (ForAll' {} : qs, q, Witness (ValueTree Nothing w1s))) ->
        Witness . ValueTree Nothing
          <$> sequence
            [ rec ([], p, w0) (qs, q, w1) <&> (^. #unWitness)
              | w1 <- Witness <$> w1s
            ]
      (([], _, _), (ForAll' {} : _, _, _)) ->
        Left (ErrorMessage () "expected a universal quantifier shaped witness on the right")
      ((ForSome' {} : qs, p, Witness (ValueTree (Just f) [w0])), ([], q, w1)) ->
        Witness . ValueTree (Just f) . (: []) . (^. #unWitness)
          <$> rec (qs, p, Witness w0) ([], q, w1)
      ((ForSome' {} : _, _, _), ([], _, _)) ->
        Left (ErrorMessage () "expected an existential quantifier shaped witness on the left")
      (([], p, w0), (ForSome' {} : qs, q, Witness (ValueTree (Just f) [w1]))) ->
        Witness . ValueTree (Just f) . (: []) . (^. #unWitness)
          <$> rec ([], p, w0) (qs, q, Witness w1)
      (([], _, _), (ForSome' {} : _, _, _)) ->
        Left (ErrorMessage () "expected an existential quantifier shaped witness on the right")
  where
    rec = mergeWitnessesConjunctive

zipAndPad :: a -> [a] -> b -> [b] -> [(a, b)]
zipAndPad _ [] _ [] = []
zipAndPad a [] _ (b1 : bs) = (a, b1) : zipAndPad a [] b1 bs
zipAndPad _ (a1 : as) b [] = (a1, b) : zipAndPad a1 as b []
zipAndPad _ (a1 : as) _ (b1 : bs) = (a1, b1) : zipAndPad a1 as b1 bs

-- Has the effect of putting a negation in front of a quantifier string
-- and then carrying it through to the end, preserving semantics.
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
    ForAll' x b ->
      pure (ForSome' (someFirstOrder x b))
    ForSome' (Some x _ [] (OutputBound b)) ->
      pure (ForAll' x b)
    ForSome' _ ->
      Left . ErrorMessage ann $
        "not supported: second-order quantification in negative position"
    Given' (Instance x n ibs ob) ->
      pure (Given' (Instance x n ibs ob))
