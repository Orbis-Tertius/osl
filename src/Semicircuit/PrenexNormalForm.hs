{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}


module Semicircuit.PrenexNormalForm
  ( toStrongPrenexNormalForm
  , toPrenexNormalForm
  ) where


import OSL.Types.ErrorMessage (ErrorMessage (..))
import Semicircuit.Types.Sigma11 (Formula (..), Quantifier (..), ExistentialQuantifier (..), someFirstOrder, OutputBound (..))


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
toStrongPrenexNormalForm = todo


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
    Iff _ _ ->
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


todo :: a
todo = todo
