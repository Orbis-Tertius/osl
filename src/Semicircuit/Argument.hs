{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Semicircuit.Argument
  ( getNameValues
  ) where

import Control.Lens ((^.))
import Control.Monad (foldM)
import Data.Map (Map)
import qualified Data.Map as Map
import OSL.Types.Sigma11.Argument (Argument (Argument), Statement (Statement), Witness (Witness))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.Sigma11.Value (Value)
import OSL.Types.Sigma11.ValueTree (ValueTree (ValueTree))
import Semicircuit.Types.Semicircuit (Semicircuit)
import Semicircuit.Types.Sigma11 (Name, InstanceQuantifier, ExistentialQuantifier)

-- Gets a map from instance and existential names
-- to their assigned values. This makes sense for
-- semicircuits because all universal quantifiers
-- have been pushed down, so each instance or
-- existential name has a unique value.
getNameValues ::
  forall ann.
  ann ->
  Semicircuit ->
  Argument ->
  Either (ErrorMessage ann) (Map Name Value)
getNameValues ann f arg0 = do
  (arg1, m1) <- foldM (iq ann) (arg0, mempty) (f ^. #formula . #quantifiers . #instanceQuantifiers)
  snd <$> foldM (eq ann) (arg1, m1) (f ^. #formula . #quantifiers . #existentialQuantifiers)
  where
    iq :: forall ann. ann -> (Argument, Map Name Value) -> InstanceQuantifier -> Either (ErrorMessage ann) (Argument, Map Name Value)
    iq ann' (arg', m') q =
      case arg' ^. #statement . #unStatement of
        v:vs -> pure (Argument (Statement vs) (arg' ^. #witness), Map.insert (q ^. #name) v m')
        _ -> Left (ErrorMessage ann' "statement is too short")

    eq :: forall ann. ann -> (Argument, Map Name Value) -> ExistentialQuantifier -> Either (ErrorMessage ann) (Argument, Map Name Value)
    eq ann' (arg', m') q =
      case arg' ^. #witness . #unWitness of
        ValueTree (Just v) [w'] ->
          pure (Argument (arg' ^. #statement) (Witness w'), Map.insert (q ^. #name) v m')
        _ -> Left (ErrorMessage ann' "expected an existential shaped witness")
