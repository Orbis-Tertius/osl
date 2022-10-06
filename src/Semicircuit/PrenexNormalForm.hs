{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}


module Semicircuit.PrenexNormalForm
  ( toStrongPrenexNormalForm
  , toPrenexNormalForm
  ) where


import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Sigma11 (prependBounds, prependArguments)
import Semicircuit.Types.Sigma11 (Formula (..), Quantifier (..), ExistentialQuantifier (..), someFirstOrder, OutputBound (..), Name, Bound, InputBound (..))


-- Assumes input is in prenex normal form.
-- Bring all second-order quantifiers to the front,
-- along with any first-order existential quantifiers
-- preceding them. Said first-order existential
-- quantifiers become second-order existential
-- quantifiers if there are any universal quantifiers
-- preceding them. Second-order existential quantifiers
-- increase in arity when preceded by universal
-- quantifiers, becoming dependent on those universally
-- quantified values.
toStrongPrenexNormalForm
  :: ann
  -> [Quantifier]
  -> Formula
  -> Either (ErrorMessage ann) ([Quantifier], Formula)
toStrongPrenexNormalForm ann qs f =
  case qs of
    [] -> pure ([], f)
    Existential q : qs' -> do
      (qs'', f') <- rec qs' f
      pure (Existential q : qs'', f')
    Universal x b : qs' -> do
      (qs'', f') <- rec qs' f
      case qs'' of
        [] -> pure ([Universal x b], f')
        Universal _ _ : _ ->
          pure (Universal x b : qs'', f')
        Existential _ : _ ->
          pushUniversalQuantifiersDown ann [(x, b)] qs'' f'
  where
    rec = toStrongPrenexNormalForm ann


pushUniversalQuantifiersDown
  :: ann
  -> [(Name, Bound)]
  -> [Quantifier]
  -> Formula
  -> Either (ErrorMessage ann) ([Quantifier], Formula)
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
        SomeP _ _ _ _ ->
          Left . ErrorMessage ann
            $ "unsupported: permutation quantifier inside a universal quantifier"


toPrenexNormalForm
  :: ann
  -> Formula
  -> Either (ErrorMessage ann) ([Quantifier], Formula)
toPrenexNormalForm ann =
  \case
    Equal a b -> pure ([], Equal a b)
    LessOrEqual a b -> pure ([], LessOrEqual a b)
    Predicate p xs -> pure ([], Predicate p xs)
    Not p -> do
      (qs, p') <- rec p
      (, Not p') <$> flipQuantifiers ann qs
    And p q -> do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      pure (pQs <> qQs, And p' q')
    Or p q -> do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      pure (pQs <> qQs, Or p' q')
    Implies p q -> do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      pQs' <- flipQuantifiers ann pQs
      pure (pQs' <> qQs, Implies p' q')
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
  where
    rec = toPrenexNormalForm ann


flipQuantifiers
  :: ann
  -> [Quantifier]
  -> Either (ErrorMessage ann) [Quantifier]
flipQuantifiers ann qs =
  mapM (flipQuantifier ann) qs


flipQuantifier
  :: ann
  -> Quantifier
  -> Either (ErrorMessage ann) Quantifier
flipQuantifier ann =
  \case
    Universal x b ->
      pure (Existential (someFirstOrder x b))
    Existential (Some x _ [] (OutputBound b)) ->
      pure (Universal x b)
    Existential _ ->
      Left . ErrorMessage ann $
        "not supported: second-order quantification in negative position"
