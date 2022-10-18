{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

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
import Control.Monad (replicateM)
import Control.Monad.State (State, evalState, get, put)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Halo2.Types.Circuit (Circuit (..), LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnTypes (ColumnTypes)
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
import Semicircuit.Types.PNFFormula (UniversalQuantifier, ExistentialQuantifier (Some, SomeP))
import Semicircuit.Types.Semicircuit (Semicircuit)
import Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout (..), NameMapping (NameMapping), OutputMapping (..), TermMapping (..), DummyRowAdviceColumn, FixedColumns, ArgMapping (..))
import Semicircuit.Types.Sigma11 (Name, Term)

type Layout = SemicircuitToLogicCircuitColumnLayout

semicircuitToLogicCircuit
  :: FiniteField
  -> RowCount
  -> Semicircuit
  -> LogicCircuit
semicircuitToLogicCircuit fp rowCount x =
  let layout = columnLayout x in
  Circuit fp
  (layout ^. #columnTypes)
  (equalityConstrainableColumns x layout)
  (gateConstraints x layout)
  (lookupArguments x layout)
  rowCount
  (equalityConstraints x layout)
  (fixedValues rowCount layout)


newtype S = S ColumnIndex


nextCol :: State S ColumnIndex
nextCol = do
  S x <- get
  put (S (x+1))
  pure x


columnLayout :: Semicircuit -> Layout
columnLayout x =
  flip evalState (S 0) $ do
    nm <- nameMappings x
    tm <- termMappings x
    dr <- dummyRowAdviceColumn x
    fs <- fixedColumns x
    pure $
      SemicircuitToLogicCircuitColumnLayout
      (columnTypes x nm tm dr fs)
      nm tm fs dr


columnTypes
  :: Semicircuit
  -> Map Name NameMapping
  -> Map Term TermMapping
  -> DummyRowAdviceColumn
  -> FixedColumns
  -> ColumnTypes
columnTypes = todo


nameMappings :: Semicircuit -> State S (Map Name NameMapping)
nameMappings x =
  mconcat <$> sequence
  [ freeVariableMappings x
  , universalVariableMappings x
  , existentialVariableMappings x
  ]


universalVariableMappings :: Semicircuit -> State S (Map Name NameMapping)
universalVariableMappings x =
  Map.fromList <$> sequence
  (universalVariableMapping <$>
     x ^. #formula . #quantifiers . #universalQuantifiers)


universalVariableMapping
  :: UniversalQuantifier
  -> State S (Name, NameMapping)
universalVariableMapping v =
  (v ^. #name, )
    <$> (NameMapping <$> (OutputMapping <$> nextCol)
                     <*> pure [])


existentialVariableMappings
  :: Semicircuit
  -> State S (Map Name NameMapping)
existentialVariableMappings x =
  Map.fromList <$> sequence
  (existentialVariableMapping <$>
     x ^. #formula . #quantifiers . #existentialQuantifiers)


existentialVariableMapping
  :: ExistentialQuantifier -> State S (Name, NameMapping)
existentialVariableMapping =
  \case
    Some x _ _ _ ->
      (x,) <$>
        (NameMapping
          <$> (OutputMapping <$> nextCol)
          <*> replicateM (x ^. #arity . #unArity)
                (ArgMapping <$> nextCol))
    SomeP x _ _ _ ->
      (x,) <$>
        (NameMapping
          <$> (OutputMapping <$> nextCol)
          <*> (((:[]) . ArgMapping) <$> nextCol))


freeVariableMappings :: Semicircuit -> State S (Map Name NameMapping)
freeVariableMappings x =
  Map.fromList <$> sequence
  (freeVariableMapping <$>
    Set.toList (x ^. #freeVariables . #unFreeVariables))


freeVariableMapping :: Name -> State S (Name, NameMapping)
freeVariableMapping x =
  (x,) <$>
    (NameMapping
      <$> (OutputMapping <$> nextCol)
      <*> (replicateM (x ^. #arity . #unArity)
            (ArgMapping <$> nextCol)))


termMappings :: Semicircuit -> State S (Map Term TermMapping)
termMappings x =
  Map.fromList <$> sequence
  (termMapping <$>
    Set.toList (x ^. #adviceTerms . #unAdviceTerms))


termMapping :: Term -> State S (Term, TermMapping)
termMapping t = (t,) . TermMapping <$> nextCol


fixedColumns :: Semicircuit -> State S FixedColumns
fixedColumns = todo


dummyRowAdviceColumn :: Semicircuit -> State S DummyRowAdviceColumn
dummyRowAdviceColumn = todo


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
  EqualityConstrainableColumns . Set.fromList
    $ [layout ^. #fixedColumns . #zeroVector
               . #unZeroVectorIndex]
      <> (universalToColumnIndex layout <$>
        (x ^. #formula . #quantifiers . #universalQuantifiers))


universalToColumnIndex
  :: Layout
  -> UniversalQuantifier
  -> ColumnIndex
universalToColumnIndex layout v =
  case Map.lookup (v ^. #name) (layout ^. #nameMappings) of
    Just m -> m ^. #outputMapping . #unOutputMapping
    Nothing -> die "universalToColumnIndex: failed lookup (this is a compiler bug)"


gateConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
gateConstraints x layout =
  mconcat
  [ instanceFunctionTablesDefineFunctionsConstraints x layout
  , existentialFunctionTablesDefineFunctionsConstraints x layout
  , firstOrderInstanceVariableColumnsAreUniformConstraints x layout
  , quantifierFreeFormulaIsTrueConstraints x layout
  , dummyRowIndicatorConstraints x layout
  , lessThanIndicatorFunctionCallConstraints x layout
  , existentialOutputsInBoundsConstraints x layout
  , existentialInputsInBoundsConstraints x layout
  , universalTableConstraints x layout
  , existentialOutputIndependenceFromUniversalsConstraints x layout
  ]


instanceFunctionTablesDefineFunctionsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
instanceFunctionTablesDefineFunctionsConstraints = todo


existentialFunctionTablesDefineFunctionsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
existentialFunctionTablesDefineFunctionsConstraints = todo


firstOrderInstanceVariableColumnsAreUniformConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
firstOrderInstanceVariableColumnsAreUniformConstraints = todo


quantifierFreeFormulaIsTrueConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
quantifierFreeFormulaIsTrueConstraints = todo


dummyRowIndicatorConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
dummyRowIndicatorConstraints = todo


lessThanIndicatorFunctionCallConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
lessThanIndicatorFunctionCallConstraints = todo


existentialOutputsInBoundsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
existentialOutputsInBoundsConstraints = todo


existentialInputsInBoundsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
existentialInputsInBoundsConstraints = todo


universalTableConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
universalTableConstraints = todo


existentialOutputIndependenceFromUniversalsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
existentialOutputIndependenceFromUniversalsConstraints = todo


lookupArguments
  :: Semicircuit
  -> Layout
  -> LookupArguments
lookupArguments x layout =
  mconcat
  [ freeFunctionCallLookupArguments x layout
  , existentialFunctionCallLookupArguments x layout
  ]


freeFunctionCallLookupArguments
  :: Semicircuit
  -> Layout
  -> LookupArguments
freeFunctionCallLookupArguments = todo


existentialFunctionCallLookupArguments
  :: Semicircuit
  -> Layout
  -> LookupArguments
existentialFunctionCallLookupArguments = todo



todo :: a
todo = todo
