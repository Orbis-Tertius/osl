{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module Semicircuit.LiftSecondOrderQuantifiers
  ( liftSecondOrderQuantifiers
  ) where


import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.Sigma11 (Formula (..), ExistentialQuantifier (..))


-- Bring all second-order quantifiers to the front,
-- along with any first-order existential quantifiers
-- preceding them. Said first-order existential
-- quantifiers become second-order existential
-- quantifiers if there are any universal quantifiers
-- preceding them. Second-order existential quantifiers
-- increase in arity when preceded by universal
-- quantifiers, becoming dependent on those universally
-- quantified values.
liftSecondOrderQuantifiers
  :: ann
  -> Formula
  -> Either (ErrorMessage ann) Formula
liftSecondOrderQuantifiers ann a = do
  (qs, a') <- liftSecondOrderQuantifiers' ann a
  pure $ foldl (flip Exists) a' qs


liftSecondOrderQuantifiers'
  :: ann
  -> Formula
  -> Either (ErrorMessage ann)
       ([ExistentialQuantifier], Formula)
liftSecondOrderQuantifiers' ann =
  \case
    Equal a b -> pure ([], Equal a b)
    LessOrEqual a b -> pure ([], LessOrEqual a b)
    Predicate p as -> pure ([], Predicate p as)
    Not p -> do
      (qs, p') <- rec p
      case qs of
        [] -> pure ([], Not p')
        _ -> Left . ErrorMessage ann
          $ "second-order quantifier preceded by negation"
    And p q -> rec' And p q
    Or p q -> rec' Or p q
    _ -> todo
  where
    rec = liftSecondOrderQuantifiers' ann

    rec' f p q = do
      (pQs, p') <- rec p
      (qQs, q') <- rec q
      -- TODO consistent variable naming
      pure (pQs <> qQs, f p' q')


todo :: a
todo = todo
