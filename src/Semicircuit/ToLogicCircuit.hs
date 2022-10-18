{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import qualified Data.Map as Map
import qualified Data.Set as Set
import Halo2.Types.Circuit (Circuit (..), LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns (..))
import Halo2.Types.EqualityConstraint (EqualityConstraint (..))
import Halo2.Types.EqualityConstraints (EqualityConstraints (..))
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.FixedColumn (FixedColumn (..))
import Halo2.Types.FixedValues (FixedValues (..))
import Halo2.Types.RowCount (RowCount (..))
import Die (die)
import Semicircuit.Types.Semicircuit (Semicircuit, UniversalVariable (..))
import Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout)

type Layout = SemicircuitToLogicCircuitColumnLayout

semicircuitToLogicCircuit
  :: FiniteField
  -> Semicircuit
  -> LogicCircuit
semicircuitToLogicCircuit fp x =
  let layout = columnLayout x
      nRows = rowCount x layout in
  Circuit fp
  (layout ^. #columnTypes)
  (equalityConstrainableColumns x layout)
  (gateConstraints x layout)
  (lookupArguments x layout)
  nRows
  (equalityConstraints x layout)
  (fixedValues nRows layout)


columnLayout :: Semicircuit -> Layout
columnLayout = todo


fixedValues :: RowCount -> Layout -> FixedValues
fixedValues (RowCount n) layout =
  FixedValues . Map.fromList $
  [ ( layout ^. #fixedColumns . #zeroVector
              . #unZeroVectorIndex
    , FixedColumn $ replicate n 0 )
  , ( layout ^. #fixedColumns . #oneVector
              . #unOneVectorIndex
    , FixedColumn $ replicate n 1 )
  , ( layout ^. #fixedColumns . #lastRowIndicator
              . #unLastRowIndicatorColumnIndex
    , FixedColumn $ replicate (n-1) 0 <> [1] )
  ]


equalityConstraints
  :: Semicircuit
  -> Layout
  -> EqualityConstraints
equalityConstraints x layout =
  EqualityConstraints
  [ EqualityConstraint
    $
    [ PolynomialVariable
      (layout ^. #fixedColumns . #zeroVector
               . #unZeroVectorIndex)
      0
    ] <> Set.fromList
      [ PolynomialVariable u 0
      | u :: ColumnIndex
          <-   (^. #outputMapping . #unOutputMapping)
             . flip (Map.findWithDefault
               (die "failed lookup in equalityConstraints"))
               (layout ^. #nameMappings)
             . (^. #name)
             <$>
             x ^. #formula . #quantifiers
               . #universalQuantifiers
      ]
  ]


equalityConstrainableColumns
  :: Semicircuit
  -> Layout
  -> EqualityConstrainableColumns
equalityConstrainableColumns x layout =
  EqualityConstrainableColumns
    $ (universalToColumnIndex layout
      `Set.map`
      (x ^. #universalVariables . #unUniversalVariables))
      <> Set.singleton
         (layout ^. #fixedColumns . #zeroVector
                  . #unZeroVectorIndex)


universalToColumnIndex
  :: Layout
  -> UniversalVariable
  -> ColumnIndex
universalToColumnIndex layout v =
  case Map.lookup (v ^. #name) (layout ^. #nameMappings) of
    Just m -> m ^. #outputMapping . #unOutputMapping
    Nothing -> die "universalToColumnIndex: failed lookup (this is a compiler bug)"


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
