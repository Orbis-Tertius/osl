{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLabels #-}

module Halo2.AIR
  ( toCircuit,
    fromCircuit
  ) where

import Halo2.Prelude
import Halo2.Types.AIR (AIR (AIR))
import Halo2.Types.Circuit (Circuit (Circuit))

-- Each AIR defines a circuit, which has no lookup arguments or equality
-- constraints.
toCircuit :: AIR a -> Circuit a
toCircuit a =
  Circuit
  (a ^. #columnTypes)
  mempty
  (a ^. #gateConstraints)
  mempty
  (a ^. #rowCount)
  mempty
  (a ^. #fixedValues)

-- Each circuit defines an AIR, by forgetting its lookup arguments and
-- equality constraints.
fromCircuit :: Circuit a -> AIR a
fromCircuit c =
  AIR
  (c ^. #columnTypes)
  (c ^. #gateConstraints)
  (c ^. #rowCount)
  (c ^. #fixedValues)
