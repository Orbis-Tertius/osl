{-# LANGUAGE OverloadedLabels #-}

module Semicircuit.ToLogicCircuit
  ( semicircuitToLogicCircuit
  , columnLayout
  , fixedValues
  , equalityConstraints
  , equalityConstrainableColumns
  , gateConstraints
  , lookupArguments
  ) where


import Control.Lens ((^.))
import Halo2.Types.Circuit (Circuit (..), LogicCircuit)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns)
import Halo2.Types.EqualityConstraints (EqualityConstraints)
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.RowCount (RowCount)
import Semicircuit.Types.Semicircuit (Semicircuit)
import Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout)

type Layout = SemicircuitToLogicCircuitColumnLayout

semicircuitToLogicCircuit
  :: FiniteField
  -> Semicircuit
  -> LogicCircuit
semicircuitToLogicCircuit fp x =
  let layout = columnLayout x in
  Circuit fp
  (layout ^. #columnTypes)
  (equalityConstrainableColumns x layout)
  (gateConstraints x layout)
  (lookupArguments x layout)
  (rowCount x layout)
  (equalityConstraints x layout)
  (fixedValues layout)


columnLayout :: Semicircuit -> Layout
columnLayout = todo


fixedValues :: Layout -> FixedValues
fixedValues = todo


equalityConstraints
  :: Semicircuit
  -> Layout
  -> EqualityConstraints
equalityConstraints = todo


equalityConstrainableColumns
  :: Semicircuit
  -> Layout
  -> EqualityConstrainableColumns
equalityConstrainableColumns = todo


gateConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
gateConstraints = todo


lookupArguments
  :: Semicircuit
  -> Layout
  -> LookupArguments
lookupArguments = todo


rowCount
  :: Semicircuit
  -> Layout
  -> RowCount
rowCount = todo


todo :: a
todo = todo
