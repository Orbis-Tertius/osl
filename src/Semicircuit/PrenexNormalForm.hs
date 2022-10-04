{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}


module Semicircuit.PrenexNormalForm
  ( toPrenexNormalForm
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
toPrenexNormalForm
  :: ann
  -> Formula
  -> Either (ErrorMessage ann) Formula
toPrenexNormalForm ann a = todo


todo :: a
todo = todo
