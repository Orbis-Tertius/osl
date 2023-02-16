{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Semicircuit.ToLogicCircuit
  ( semicircuitToLogicCircuit,
    semicircuitArgumentToLogicCircuitArgument,
    columnLayout,
    fixedValues,
    equalityConstraints,
    equalityConstrainableColumns,
    gateConstraints,
    instanceFunctionTablesDefineFunctionsConstraints,
    existentialFunctionTablesDefineFunctionsConstraints,
    quantifierFreeFormulaIsTrueConstraints,
    dummyRowIndicatorConstraints,
    existentialOutputsInBoundsConstraints,
    existentialInputsInBoundsConstraints,
    universalTableConstraints,
  )
where

import Cast (intToInteger, integerToInt, word64ToInteger)
import Control.Lens ((<&>), (^.))
import Control.Monad (foldM, forM, replicateM)
import Control.Monad.State (State, evalState, get, put)
import Data.Either.Extra (mapLeft)
import Data.List.Extra (foldl', (!?))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text, pack)
import Die (die)
import Halo2.Circuit (rowsToCellMap)
import Halo2.LogicConstraint (constantFoldConstraints)
import qualified Halo2.Types.Argument as Halo2
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.Circuit (Circuit (..), LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import qualified Halo2.Types.ColumnType as ColType
import Halo2.Types.ColumnTypes (ColumnTypes (..))
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns (..))
import Halo2.Types.EqualityConstraint (EqualityConstraint (..))
import Halo2.Types.EqualityConstraints (EqualityConstraints (..))
import Halo2.Types.FixedBound (FixedBound (FixedBound), boolBound, integerToFixedBound)
import Halo2.Types.FixedColumn (FixedColumn (..))
import Halo2.Types.FixedValues (FixedValues (..))
import Halo2.Types.InputExpression (InputExpression (..))
import Halo2.Types.Label (Label (Label))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top))
import qualified Halo2.Types.LogicConstraint as LC
import Halo2.Types.LogicConstraints (LogicConstraints (..))
import Halo2.Types.LookupTableColumn (LookupTableColumn (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.RowCount (RowCount (..))
import Halo2.Types.RowIndex (RowIndex (..), RowIndexType (Absolute, Relative))
import qualified OSL.Sigma11 as S11
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import qualified OSL.Types.Sigma11.Argument as S11
import qualified OSL.Types.Sigma11.EvaluationContext as S11
import OSL.Types.Sigma11.Value (Value (Value))
import Semicircuit.Argument (getNameValues)
import Semicircuit.Sigma11 (existentialQuantifierInputBounds, existentialQuantifierName, existentialQuantifierOutputBound, getInputName)
import Semicircuit.Types.PNFFormula (ExistentialQuantifier, ExistentialQuantifierF (Some, SomeP), InstanceQuantifier, InstanceQuantifierF (Instance), UniversalQuantifier (All))
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Semicircuit (Semicircuit)
import Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout (ArgMapping (..), DummyRowAdviceColumn (..), FixedColumns (..), LastRowIndicatorColumnIndex (..), NameMapping (NameMapping), OutputMapping (..), SemicircuitToLogicCircuitColumnLayout (..))
import Semicircuit.Types.Sigma11 (Bound, BoundF (FieldMaxBound, TermBound), InputBound, Name, OutputBound, OutputBoundF (OutputBound), Term, TermF (Add, App, AppInverse, Const, IndLess, Max, Mul))
import Stark.Types.Scalar (Scalar, integerToScalar, one, order, scalarToInt, scalarToInteger, zero)

type Layout = SemicircuitToLogicCircuitColumnLayout

semicircuitToLogicCircuit ::
  RowCount ->
  Semicircuit ->
  (LogicCircuit, Layout)
semicircuitToLogicCircuit rowCount x =
  let layout = columnLayout x
   in ( Circuit
          (layout ^. #columnTypes)
          (equalityConstrainableColumns x layout)
          (constantFoldConstraints (columnBounds x layout (gateConstraints x layout)))
          mempty
          rowCount
          (equalityConstraints x layout)
          (fixedValues rowCount layout),
        layout
      )

semicircuitArgumentToLogicCircuitArgument ::
  ann ->
  RowCount ->
  Semicircuit ->
  Layout ->
  S11.Argument ->
  Either (ErrorMessage ann) Halo2.Argument
semicircuitArgumentToLogicCircuitArgument ann rc f layout arg = do
  vals <- getNameValues ann f arg
  mconcat
    <$> sequence
      [ getUniversalTableArgument ann rc f layout vals,
        nameValuesToLogicCircuitArgument ann rc f layout vals,
        getFixedValuesArgument ann rc layout
      ]

getUniversalTableArgument ::
  ann ->
  RowCount ->
  Semicircuit ->
  Layout ->
  Map Name Value ->
  Either (ErrorMessage ann) Halo2.Argument
getUniversalTableArgument ann (RowCount n) f layout vs = do
  t <- getUniversalTable ann (f ^. #formula . #quantifiers . #universalQuantifiers) layout vs
  if intToInteger (Map.size t) > n'
    then Left (ErrorMessage ann "universal table size exceeds row count")
    else
      Halo2.Argument mempty . Halo2.Witness . rowsToCellMap . Map.fromList
        <$> pad n' (Map.toList t)
  where
    n' = scalarToInteger n

    pad 0 _ = pure []
    pad _ [] = Left (ErrorMessage ann "empty universal table")
    pad n'' [(i, x)] = ((i, x) :) <$> pad (n'' - 1) [(i + 1, x)]
    pad n'' ((i, x) : xs) = ((i, x) :) <$> pad (n'' - 1) xs

getUniversalTable ::
  forall ann.
  ann ->
  [UniversalQuantifier] ->
  Layout ->
  Map Name Value ->
  Either (ErrorMessage ann) (Map (RowIndex 'Absolute) (Map ColumnIndex Scalar))
getUniversalTable _ [] _ _ = pure mempty
getUniversalTable ann [All x b] layout vs = do
  let ec = S11.EvaluationContext (Map.mapKeys Left vs)
      dummyCol = layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn
  outCol <-
    case Map.lookup x (layout ^. #nameMappings) of
      Just nm -> pure (nm ^. #outputMapping . #unOutputMapping)
      Nothing -> Left (ErrorMessage ann "name not defined in circuit layout")
  b' <-
    mapLeft (\(ErrorMessage () msg) -> ErrorMessage ann msg) $
      S11.evalTerm ec b
  if b' == zero
    then
      pure . Map.singleton (0 :: RowIndex 'Absolute) $
        Map.fromList [(dummyCol, one), (outCol, zero)]
    else
      pure . Map.fromList $
        [ (RowIndex ri, Map.fromList [(dummyCol, zero), (outCol, si)])
          | i <- [0 .. scalarToInteger b' - 1],
            let ri =
                  fromMaybe
                    (die "Semicircuit.ToLogicCircuit.getUniversalTable: value out of range of Int")
                    (integerToInt i),
            let si =
                  fromMaybe
                    (die "Semicircuit.ToLogicCircuit.getUniversalTable: value out of range of scalar")
                    (integerToScalar i)
        ]
getUniversalTable ann qs@(All x b : qs') layout vs = do
  let ec = S11.EvaluationContext (Map.mapKeys Left vs)
      dummyCol = layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn
  outCols <- forM qs $ \(All x' _) ->
    case Map.lookup x' (layout ^. #nameMappings) of
      Just nm -> pure (nm ^. #outputMapping . #unOutputMapping)
      Nothing -> Left (ErrorMessage ann "name not defined in circuit layout")
  outCol <-
    case outCols of
      (outCol' : _) -> pure outCol'
      _ -> Left (ErrorMessage ann "unreachable case in getUniversalTable (this is a bug)")
  b' <-
    mapLeft (\(ErrorMessage () msg) -> ErrorMessage ann msg) $
      S11.evalTerm ec b
  if b' == zero
    then
      pure . Map.singleton (0 :: RowIndex 'Absolute)
        . Map.fromList
        $ [(dummyCol, one)] <> ((,zero) <$> outCols)
    else foldM (f outCol) mempty ([0 .. scalarToInteger b' - 1] :: [Integer])
  where
    f ::
      ColumnIndex ->
      Map (RowIndex 'Absolute) (Map ColumnIndex Scalar) ->
      Integer ->
      Either (ErrorMessage ann) (Map (RowIndex 'Absolute) (Map ColumnIndex Scalar))
    f outCol t v = do
      v' <-
        maybe
          (Left (ErrorMessage ann "value out of range of scalar field"))
          pure
          (integerToScalar v)
      let vs' = Map.insert x (Value (Map.singleton [] v')) vs
      t' <- getUniversalTable ann qs' layout vs'
      let j = maybe 0 ((+ 1) . fst . fst) (Map.maxViewWithKey t)
          t'' = Map.insert outCol v' <$> Map.mapKeys (+ j) t'
      pure (t <> t'')

nameValuesToLogicCircuitArgument ::
  ann ->
  RowCount ->
  Semicircuit ->
  Layout ->
  Map Name Value ->
  Either (ErrorMessage ann) Halo2.Argument
nameValuesToLogicCircuitArgument ann rc f layout vs =
  Halo2.Argument
    <$> ( Halo2.Statement . mconcat
            <$> sequence
              [ nameMappingArgument ann rc nm v
                | (n, (nm, v)) <-
                    Map.toList $
                      Map.intersectionWith (,) (layout ^. #nameMappings) vs,
                  n `Set.member` Set.fromList ((f ^. #formula . #quantifiers . #instanceQuantifiers) <&> (^. #name))
              ]
        )
    <*> ( Halo2.Witness . mconcat
            <$> sequence
              [ nameMappingArgument ann rc nm v
                | (n, (nm, v)) <-
                    Map.toList $
                      Map.intersectionWith (,) (layout ^. #nameMappings) vs,
                  n `Set.member` Set.fromList ((f ^. #formula . #quantifiers . #existentialQuantifiers) <&> (^. #name))
              ]
        )

nameMappingArgument ::
  ann ->
  RowCount ->
  NameMapping ->
  Value ->
  Either (ErrorMessage ann) (Map CellReference Scalar)
nameMappingArgument ann (RowCount n) nm (Value f) =
  if intToInteger (Map.size f) > n'
    then Left (ErrorMessage ann "value cardinality exceeds row count")
    else do
      indices <- mapM sToI [0 .. n' - 1]
      let f' = Map.toList f
      (defaultIns, defaultOut) <-
        case reverse f' of
          ((xs, y) : _) -> pure (xs, y)
          _ -> Left (ErrorMessage ann "empty value")
      pure $
        Map.fromList
          ( [ (CellReference ci ri, x)
              | let ci = nm ^. #outputMapping . #unOutputMapping,
                (ri, x) <- zip indices ((snd <$> f') <> repeat defaultOut)
            ]
          )
          <> Map.fromList
            ( [ (CellReference ci ri, x)
                | (ri, inputs) <- zip indices ((fst <$> f') <> repeat defaultIns),
                  (ci, x) <- zip ((nm ^. #argMappings) <&> (^. #unArgMapping)) inputs
              ]
            )
  where
    n' = scalarToInteger n
    sToI = maybe (Left (ErrorMessage ann "index is out of range of Int")) (pure . RowIndex) . integerToInt

getFixedValuesArgument ::
  ann ->
  RowCount ->
  Layout ->
  Either (ErrorMessage ann) Halo2.Argument
getFixedValuesArgument ann (RowCount n) layout = do
  n' <-
    maybe
      (Left (ErrorMessage ann "row count of range of Int"))
      pure
      (integerToInt (scalarToInteger n))
  pure . Halo2.Argument mempty . Halo2.Witness . Map.fromList $
    [ ( CellReference
          (layout ^. #fixedColumns . #lastRowIndicator . #unLastRowIndicatorColumnIndex)
          (RowIndex ri),
        v
      )
      | ri <- [0 .. n' - 1],
        let v = if ri == n' - 1 then one else zero
    ]

newtype S = S (ColumnIndex, ColumnTypes)

nextCol :: ColType.ColumnType -> State S ColumnIndex
nextCol t = do
  S (x, ts) <- get
  put $ S (x + 1, ts <> ColumnTypes (Map.singleton x t))
  pure x

columnLayout :: Semicircuit -> Layout
columnLayout x =
  flip evalState (S (0, mempty)) $ do
    nm <- nameMappings x
    dr <- DummyRowAdviceColumn <$> nextCol ColType.Advice
    fs <- fixedColumns
    S (_, colTypes) <- get
    pure $
      SemicircuitToLogicCircuitColumnLayout
        colTypes
        nm
        fs
        dr

nameMappings :: Semicircuit -> State S (Map Name NameMapping)
nameMappings x =
  mconcat
    <$> sequence
      [ freeVariableMappings x,
        instanceQuantifiersMappings x,
        universalVariableMappings x,
        existentialQuantifiersMappings x
      ]

universalVariableMappings :: Semicircuit -> State S (Map Name NameMapping)
universalVariableMappings x =
  Map.fromList
    <$> mapM
      universalVariableMapping
      (x ^. #formula . #quantifiers . #universalQuantifiers)

universalVariableMapping ::
  UniversalQuantifier ->
  State S (Name, NameMapping)
universalVariableMapping v =
  (v ^. #name,)
    <$> ( NameMapping <$> (OutputMapping <$> nextCol ColType.Advice)
            <*> pure []
        )

instanceQuantifiersMappings :: Semicircuit -> State S (Map Name NameMapping)
instanceQuantifiersMappings x =
  mconcat
    <$> mapM
      instanceQuantifierMappings
      (x ^. #formula . #quantifiers . #instanceQuantifiers)

instanceQuantifierMappings ::
  InstanceQuantifier ->
  State S (Map Name NameMapping)
instanceQuantifierMappings q = do
  outMapping <- OutputMapping <$> nextCol ColType.Instance
  argMappings <-
    replicateM
      (q ^. #name . #arity . #unArity)
      (ArgMapping <$> nextCol ColType.Instance)
  pure . Map.fromList $
    [(q ^. #name, NameMapping outMapping argMappings)]
      <> catMaybes
        [ (,NameMapping (OutputMapping (m ^. #unArgMapping)) [])
            <$> getInputName ib
          | (ib, m) <- zip (q ^. #inputBounds) argMappings
        ]

existentialQuantifiersMappings ::
  Semicircuit ->
  State S (Map Name NameMapping)
existentialQuantifiersMappings x =
  mconcat
    <$> mapM
      existentialQuantifierMappings
      (x ^. #formula . #quantifiers . #existentialQuantifiers)

existentialQuantifierMappings ::
  ExistentialQuantifier -> State S (Map Name NameMapping)
existentialQuantifierMappings =
  \case
    Some x _ ibs _ -> do
      outMapping <- OutputMapping <$> nextCol ColType.Advice
      argMappings <-
        replicateM
          (x ^. #arity . #unArity)
          (ArgMapping <$> nextCol ColType.Advice)
      pure . Map.fromList $
        [(x, NameMapping outMapping argMappings)]
          <> catMaybes
            [ (,NameMapping (OutputMapping (m ^. #unArgMapping)) [])
                <$> getInputName ib
              | (ib, m) <- zip ibs argMappings
            ]
    SomeP x _ ib _ -> do
      outMapping <- OutputMapping <$> nextCol ColType.Advice
      argMapping <- ArgMapping <$> nextCol ColType.Advice
      pure . Map.fromList $
        [(x, NameMapping outMapping [argMapping])]
          <> catMaybes
            [ (,NameMapping (OutputMapping (argMapping ^. #unArgMapping)) [])
                <$> getInputName ib
            ]

freeVariableMappings :: Semicircuit -> State S (Map Name NameMapping)
freeVariableMappings x =
  Map.fromList
    <$> mapM
      freeVariableMapping
      (Set.toList (x ^. #freeVariables . #unFreeVariables))

freeVariableMapping :: Name -> State S (Name, NameMapping)
freeVariableMapping x =
  (x,)
    <$> ( NameMapping
            <$> (OutputMapping <$> nextCol ColType.Instance)
            <*> replicateM
              (x ^. #arity . #unArity)
              (ArgMapping <$> nextCol ColType.Instance)
        )

fixedColumns :: State S FixedColumns
fixedColumns =
  FixedColumns . LastRowIndicatorColumnIndex
    <$> nextCol ColType.Fixed

fixedValues :: RowCount -> Layout -> FixedValues (RowIndex 'Absolute)
fixedValues (RowCount n) layout =
  FixedValues . Map.fromList $
    [ ( layout
          ^. #fixedColumns . #lastRowIndicator
            . #unLastRowIndicatorColumnIndex,
        FixedColumn . Map.fromList
          . zip (RowIndex <$> [0 .. n' - 1])
          $ replicate (n' - 1) zero <> [one]
      )
    ]
  where
    n' = scalarToInt n

equalityConstraints ::
  Semicircuit ->
  Layout ->
  EqualityConstraints
equalityConstraints x layout =
  EqualityConstraints
    [ EqualityConstraint $
        [ CellReference
            ( layout
                ^. #fixedColumns . #lastRowIndicator
                  . #unLastRowIndicatorColumnIndex -- => 0
            )
            0
        ]
          <> Set.fromList
            [ CellReference u 0
              | u :: ColumnIndex <-
                  (^. #outputMapping . #unOutputMapping)
                    . flip
                      ( Map.findWithDefault
                          (die "failed lookup in equalityConstraints")
                      )
                      (layout ^. #nameMappings)
                    . (^. #name)
                    <$> x
                      ^. #formula . #quantifiers
                        . #universalQuantifiers
            ]
    ]

equalityConstrainableColumns ::
  Semicircuit ->
  Layout ->
  EqualityConstrainableColumns
equalityConstrainableColumns x layout =
  EqualityConstrainableColumns . Set.fromList $
    [ layout
        ^. #fixedColumns . #lastRowIndicator
          . #unLastRowIndicatorColumnIndex
    ]
      <> ( universalToColumnIndex layout
             <$> (x ^. #formula . #quantifiers . #universalQuantifiers)
         )

universalToColumnIndex ::
  Layout ->
  UniversalQuantifier ->
  ColumnIndex
universalToColumnIndex layout v =
  case Map.lookup (v ^. #name) (layout ^. #nameMappings) of
    Just m -> m ^. #outputMapping . #unOutputMapping
    Nothing -> die "universalToColumnIndex: failed lookup (this is a compiler bug)"

gateConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
gateConstraints x layout =
  mconcat
    [ instanceFunctionTablesDefineFunctionsConstraints x layout,
      existentialFunctionTablesDefineFunctionsConstraints x layout,
      quantifierFreeFormulaIsTrueConstraints x layout,
      dummyRowIndicatorConstraints x layout,
      existentialOutputsInBoundsConstraints x layout,
      existentialInputsInBoundsConstraints x layout,
      universalTableConstraints x layout
    ]

columnBounds ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  LogicConstraints
columnBounds x layout =
  dummyRowAdviceColumnBounds layout
    . fixedColumnBounds layout
    . universalTableBounds x layout
    . existentialFunctionTableColumnBounds x layout
    . instanceColumnBounds x layout

instanceColumnBounds ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  LogicConstraints
instanceColumnBounds x layout =
  foldl'
    (.)
    id
    ( reverse $
        instanceQuantifierBounds x layout
          <$> (x ^. #formula . #quantifiers . #instanceQuantifiers)
    )

instanceQuantifierBounds ::
  Semicircuit ->
  Layout ->
  InstanceQuantifier ->
  LogicConstraints ->
  LogicConstraints
instanceQuantifierBounds x layout (Instance name _ inBounds outBound) =
  quantifierBounds "instance" x layout name inBounds outBound

quantifierBounds ::
  Text ->
  Semicircuit ->
  Layout ->
  Name ->
  [InputBound] ->
  OutputBound ->
  LogicConstraints ->
  LogicConstraints
quantifierBounds what x layout name inBounds outBound =
  boundToFixedBound
    x
    layout
    outputCol
    (outBound ^. #unOutputBound)
    . foldl'
      (.)
      id
      ( uncurry (boundToFixedBound x layout)
          <$> zip inputCols (inBounds <&> (^. #bound))
      )
  where
    outputCol :: ColumnIndex
    outputCol = mapping ^. #outputMapping . #unOutputMapping

    inputCols :: [ColumnIndex]
    inputCols =
      (mapping ^. #argMappings)
        <&> (^. #unArgMapping)

    mapping :: NameMapping
    mapping =
      fromMaybe
        ( die $
            what
              <> " quantifierBounds: mapping lookup failed (this is a compiler bug)\n"
              <> pack (show (name, layout ^. #nameMappings))
        )
        $ Map.lookup name (layout ^. #nameMappings)

boundToFixedBound ::
  Semicircuit ->
  Layout ->
  ColumnIndex ->
  Bound ->
  LogicConstraints ->
  LogicConstraints
boundToFixedBound x layout i =
  \case
    FieldMaxBound ->
      ( <>
          LogicConstraints
            mempty
            (Map.singleton i (FixedBound order))
      )
    TermBound b ->
      \constraints ->
        constraints
          <> LogicConstraints
            mempty
            ( Map.singleton
                i
                (termToFixedBound x layout constraints b)
            )

termToFixedBound ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  Term ->
  FixedBound
termToFixedBound x layout constraints =
  \case
    Const k -> integerToFixedBound (abs k)
    App f _ -> outputBound f
    AppInverse f _ -> outputBound f
    Add y z -> rec y + rec z
    Mul y z -> rec y * rec z
    Max y z -> rec y `max` rec z
    IndLess _ _ -> boolBound
  where
    rec = termToFixedBound x layout constraints

    outputBound :: Name -> FixedBound
    outputBound f =
      case Map.lookup f (layout ^. #nameMappings) of
        Just f' ->
          case Map.lookup (f' ^. #outputMapping . #unOutputMapping) (constraints ^. #bounds) of
            Just b -> b
            Nothing ->
              die $
                "termToFixedBound: outputBound: output bound lookup failed (this is a compiler bug)\n"
                  <> pack (show (f, f', constraints ^. #bounds))
        Nothing -> die "termToFixedBound: outputBound: name mapping lookup failed (this is a compiler bug)"

existentialFunctionTableColumnBounds ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  LogicConstraints
existentialFunctionTableColumnBounds x layout =
  foldl'
    (.)
    id
    ( reverse $
        existentialQuantifierBounds x layout
          <$> (x ^. #formula . #quantifiers . #existentialQuantifiers)
    )

existentialQuantifierBounds ::
  Semicircuit ->
  Layout ->
  ExistentialQuantifier ->
  LogicConstraints ->
  LogicConstraints
existentialQuantifierBounds x layout =
  \case
    Some name _ inBounds outBound ->
      quantifierBounds "existential" x layout name inBounds outBound
    SomeP name _ inBound outBound ->
      quantifierBounds "existential" x layout name [inBound] outBound

universalTableBounds ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  LogicConstraints
universalTableBounds x layout =
  foldl'
    (.)
    id
    ( universalQuantifierBounds x layout
        <$> (x ^. #formula . #quantifiers . #universalQuantifiers)
    )

universalQuantifierBounds ::
  Semicircuit ->
  Layout ->
  UniversalQuantifier ->
  LogicConstraints ->
  LogicConstraints
universalQuantifierBounds x layout (All name bound) =
  quantifierBounds "universal" x layout name [] (OutputBound (TermBound bound))

dummyRowAdviceColumnBounds ::
  Layout ->
  LogicConstraints ->
  LogicConstraints
dummyRowAdviceColumnBounds layout constraints =
  constraints
    <> LogicConstraints
      mempty
      (Map.singleton (layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn) boolBound)

fixedColumnBounds ::
  Layout ->
  LogicConstraints ->
  LogicConstraints
fixedColumnBounds layout constraints =
  constraints
    <> LogicConstraints
      mempty
      ( Map.fromList
          [ (layout ^. #fixedColumns . #lastRowIndicator . #unLastRowIndicatorColumnIndex, boolBound)
          ]
      )

lexicographicallyLessThanConstraint ::
  -- the lists are zipped to document that they have
  -- equal lengths
  [(PolynomialVariable, PolynomialVariable)] ->
  LogicConstraint
lexicographicallyLessThanConstraint ab =
  case ab of
    [] -> Bottom
    ((a, b) : ab') ->
      Atom (LC.Var a `LessThan` LC.Var b)
        `Or` ( Atom (LC.Var a `Equals` LC.Var b)
                 `And` rec ab'
             )
  where
    rec = lexicographicallyLessThanConstraint

equalsConstraint ::
  [(PolynomialVariable, PolynomialVariable)] ->
  LogicConstraint
equalsConstraint ab =
  case ab of
    [] -> Top
    ((a, b) : ab') ->
      Atom (LC.Var a `Equals` LC.Var b) `And` rec ab'
  where
    rec = equalsConstraint

instanceFunctionTablesDefineFunctionsConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
instanceFunctionTablesDefineFunctionsConstraints x layout =
  LogicConstraints
    [ ( Label ("instanceFunctionTablesDefineFunctions(" <> show v <> ")"),
        Atom (lastRowIndicator `Equals` LC.Const one)
          `Or` nextRowIsEqualConstraint layout v
          `Or` nextInputRowIsLexicographicallyGreaterConstraint layout v
      )
      | v <- (x ^. #formula . #quantifiers . #instanceQuantifiers) <&> (^. #name)
    ]
    mempty
  where
    lastRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout
          ^. #fixedColumns
            . #lastRowIndicator
            . #unLastRowIndicatorColumnIndex

nextRowIsEqualConstraint ::
  Layout ->
  Name ->
  LogicConstraint
nextRowIsEqualConstraint layout v =
  equalsConstraint (zip (vars 0) (vars 1))
  where
    vars :: RowIndex 'Relative -> [PolynomialVariable]
    vars i =
      case Map.lookup v (layout ^. #nameMappings) of
        Just nm ->
          ( PolynomialVariable
              (nm ^. #outputMapping . #unOutputMapping)
              i
              :
          )
            $ (`PolynomialVariable` i)
              . (^. #unArgMapping)
              <$> (nm ^. #argMappings)
        Nothing -> die "nextRowIsEqualConstraint: failed lookup (this is a compiler bug)"

nextInputRowIsLexicographicallyGreaterConstraint ::
  Layout ->
  Name ->
  LogicConstraint
nextInputRowIsLexicographicallyGreaterConstraint layout v =
  lexicographicallyLessThanConstraint
    (zip (vars 0) (vars 1))
  where
    vars :: RowIndex 'Relative -> [PolynomialVariable]
    vars i =
      case Map.lookup v (layout ^. #nameMappings) of
        Just nm ->
          (`PolynomialVariable` i)
            . (^. #unArgMapping)
            <$> (nm ^. #argMappings)
        Nothing -> die "nextInputRowIsLexicographicallyGreaterConstraint: failed lookup (this is a compiler bug)"

existentialFunctionTablesDefineFunctionsConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
existentialFunctionTablesDefineFunctionsConstraints x layout =
  LogicConstraints
    [ ( Label ("existentialFunctionTablesDefineFunctions(" <> show v <> ")"),
        Atom (lastRowIndicator `Equals` LC.Const one)
          `Or` nextRowIsEqualConstraint layout v
          `Or` nextInputRowIsLexicographicallyGreaterConstraint layout v
      )
      | v <-
          existentialQuantifierName
            <$> x ^. #formula . #quantifiers . #existentialQuantifiers
    ]
    mempty
  where
    lastRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout
          ^. #fixedColumns
            . #lastRowIndicator
            . #unLastRowIndicatorColumnIndex

sigma11TermToLogicConstraintTerm ::
  Layout ->
  Term ->
  LC.Term
sigma11TermToLogicConstraintTerm layout =
  \case
    App x [] ->
      case Map.lookup x names of
        Just (NameMapping (OutputMapping o) []) ->
          LC.Var . flip PolynomialVariable 0 $ o
        Just (NameMapping _ _) -> die "sigma11TermToLogicConstraintTerm: encountered empty application with non-empty name mapping (this is a compiler bug)"
        Nothing -> die $ "sigma11TermToLogicConstraintTerm: failed name mapping lookup (this is a compiler bug)\n" <> pack (show x)
    App f xs ->
      case Map.lookup f names of
        Just (NameMapping (OutputMapping o) inputs) ->
          LC.Lookup
            ( zip
                (InputExpression . rec <$> xs)
                (LookupTableColumn . (^. #unArgMapping) <$> inputs)
            )
            (LC.LookupTableOutputColumn (LookupTableColumn o))
        Nothing -> die "sigma11TermToLogicConstraintTerm: failed name mapping lookup (this is a compiler bug)"
    AppInverse f x ->
      case Map.lookup f names of
        Just (NameMapping (OutputMapping o) [input]) ->
          LC.Lookup
            [(InputExpression (rec x), LookupTableColumn o)]
            (LC.LookupTableOutputColumn (LookupTableColumn (input ^. #unArgMapping)))
        Just (NameMapping {}) ->
          die "sigma11TermToLogicConstraintTerm: expected a name mapping with exactly one input in an inverse application (this is a compiler bug)"
        Nothing -> die "sigma11TermToLogicConstraintTerm: failed name mapping lookup (this is a compiler bug)"
    Add x y -> rec x `LC.Plus` rec y
    Mul x y -> rec x `LC.Times` rec y
    IndLess x y -> rec x `LC.IndLess` rec y
    Max x y -> rec x `LC.Max` rec y
    Const x ->
      if x < word64ToInteger order
        then LC.Const (fromInteger x)
        else die $ "in termToPolynomial: constant term " <> pack (show x) <> " is greater than or equal to the field order " <> pack (show order) <> " (this is a compiler bug; should have been caught earlier)"
  where
    rec = sigma11TermToLogicConstraintTerm layout

    names :: Map Name NameMapping
    names = layout ^. #nameMappings

qfFormulaToLogicConstraint ::
  Layout ->
  QF.Formula ->
  LogicConstraint
qfFormulaToLogicConstraint layout =
  \case
    QF.Equal x y ->
      Atom (term x `Equals` term y)
    QF.LessOrEqual x y ->
      Atom (term x `Equals` term y)
        `Or` Atom (term x `LessThan` term y)
    QF.Predicate _ _ ->
      die "not implemented: compiling predicates to circuits"
    QF.Not p -> Not (rec p)
    QF.And p q -> And (rec p) (rec q)
    QF.Or p q -> Or (rec p) (rec q)
    QF.Implies p q -> Or (Not (rec p)) (rec q)
    QF.Iff p q -> Iff (rec p) (rec q)
    QF.Top -> Top
    QF.Bottom -> Bottom
  where
    rec = qfFormulaToLogicConstraint layout
    term = sigma11TermToLogicConstraintTerm layout

quantifierFreeFormulaIsTrueConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
quantifierFreeFormulaIsTrueConstraints x layout =
  LogicConstraints
    [ ( "quantifierFreeFormulaIsTrue",
        Atom (dummyRowIndicator `Equals` LC.Const one)
          `Or` qfFormulaToLogicConstraint
            layout
            (x ^. #formula . #qfFormula)
      )
    ]
    mempty
  where
    dummyRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn

dummyRowIndicatorConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
dummyRowIndicatorConstraints x layout =
  LogicConstraints
    [ ( "dummyRowIndicatorRangeCheck",
        Atom (dummyRowIndicator `Equals` LC.Const zero)
          `Or` Atom (dummyRowIndicator `Equals` LC.Const one)
      ),
      ( "dummyRowIndicatorConstraint",
        Atom (dummyRowIndicator `Equals` LC.Const zero)
          `Iff` someUniversalQuantifierBoundIsZeroConstraint x layout
      )
    ]
    mempty
  where
    dummyRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn

someUniversalQuantifierBoundIsZeroConstraint ::
  Semicircuit ->
  Layout ->
  LogicConstraint
someUniversalQuantifierBoundIsZeroConstraint x layout =
  let boundTerms = universalQuantifierBoundTerms x layout
   in foldl'
        Or
        Top
        [Atom (p `Equals` LC.Const zero) | p <- boundTerms]

universalQuantifierBoundTerms ::
  Semicircuit ->
  Layout ->
  [LC.Term]
universalQuantifierBoundTerms x layout =
  sigma11TermToLogicConstraintTerm layout . (^. #bound) <$> x
    ^. #formula . #quantifiers
      . #universalQuantifiers

existentialOutputsInBoundsConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
existentialOutputsInBoundsConstraints x layout =
  LogicConstraints
    [ ( Label ("existentialOutputsInBounds(" <> show y <> ")"),
        Atom (LessThan y bp)
      )
      | q <-
          x
            ^. #formula . #quantifiers
              . #existentialQuantifiers,
        let y = mapName $ existentialQuantifierName q,
        bp <- case existentialQuantifierOutputBound q of
          TermBound bp' -> [sigma11TermToLogicConstraintTerm layout bp']
          FieldMaxBound -> []
    ]
    mempty
  where
    mapName :: Name -> LC.Term
    mapName y =
      case Map.lookup y (layout ^. #nameMappings) of
        Just nm -> LC.Var (PolynomialVariable (nm ^. #outputMapping . #unOutputMapping) 0)
        Nothing -> die "existentialOutputsInBoundsConstraints: lookup failed (this is a compiler bug)"

existentialInputsInBoundsConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
existentialInputsInBoundsConstraints x layout =
  LogicConstraints
    [ ( Label ("existentialInputsInBounds(" <> show y <> ")"),
        Atom (LessThan y bp)
      )
      | q <-
          x
            ^. #formula . #quantifiers
              . #existentialQuantifiers,
        (i, ib) <- zip [0 ..] (existentialQuantifierInputBounds q),
        let y = name (existentialQuantifierName q) i,
        bp <- case ib ^. #bound of
          TermBound bp' -> [sigma11TermToLogicConstraintTerm layout bp']
          FieldMaxBound -> []
    ]
    mempty
  where
    name :: Name -> Int -> LC.Term
    name n i =
      case Map.lookup n (layout ^. #nameMappings) of
        Just nm ->
          case (nm ^. #argMappings) !? i of
            Just (ArgMapping j) -> LC.Var (PolynomialVariable j 0)
            Nothing ->
              die $
                "existentialInputsInBoundsConstraints: failed arg mapping lookup (this is a compiler bug)\n"
                  <> pack (show (n, i))
        Nothing -> die "existentialInputsInBoundsConstraints: failed name lookup (this is a compiler bug)"

newtype UniQIndex = UniQIndex {unUniQIndex :: Int}
  deriving newtype (Eq, Ord, Num, Enum, Show)

universalTableConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
universalTableConstraints x layout =
  LogicConstraints
    [ ( "universalTableConstraint",
        foldl'
          Or
          ( -- this is the last row
            Atom (lastRowIndicator `Equals` LC.Const one)
              `Or` foldl'
                Or
                -- all variables are maxed out and the next row looks the same
                ( foldl'
                    And
                    ( Atom ((u lastU 0 `LC.Plus` LC.Const one) `Equals` bound lastU)
                        `And` Atom (u lastU 0 `Equals` u lastU 1)
                    )
                    [ Atom ((u j 0 `LC.Plus` LC.Const one) `Equals` bound j)
                        `And` Atom (u j 1 `Equals` u j 0)
                      | j <- [0 .. lastU - 1]
                    ]
                )
                -- the next row is lexicographically next, by incrementing var j,
                -- for some j
                [next j | j <- [0 .. lastU]]
          )
          [ -- this is a dummy row
            foldl'
              And
              ( foldl'
                  And
                  (Atom (bound i `Equals` LC.Const zero))
                  [next j | j <- [0 .. i - 1]]
              )
              [ Atom (u j 0 `Equals` LC.Const zero) -- TODO is this needed?
                  `And` Atom (u j 1 `Equals` LC.Const zero)
                | j <- [i .. lastU]
              ]
            | i <- [0 .. lastU]
          ]
      )
    ]
    mempty
  where
    lastU :: UniQIndex
    lastU =
      UniQIndex $
        length
          ( x
              ^. #formula . #quantifiers
                . #universalQuantifiers
          )
          - 1

    u :: UniQIndex -> RowIndex 'Relative -> LC.Term
    u i j =
      case ( x
               ^. #formula . #quantifiers
                 . #universalQuantifiers
           )
        !? unUniQIndex i of
        Just q ->
          case Map.lookup
            (q ^. #name)
            (layout ^. #nameMappings) of
            Just nm ->
              LC.Var $
                PolynomialVariable
                  (nm ^. #outputMapping . #unOutputMapping)
                  j
            Nothing ->
              die "universalTableConstraints: failed name mapping lookup (this is a compiler bug)"
        Nothing ->
          die "universalTableConstraints: quantifier index out of range (this is a compiler bug)"

    -- the two rows are lexicographically consecutive and the result is obtained
    -- by incrementing index j
    next :: UniQIndex -> LogicConstraint
    next j =
      foldl'
        And
        ( Atom ((u j 0 `LC.Plus` LC.Const one) `Equals` u j 1)
            `And` Atom (u j 1 `LessThan` bound j)
        )
        ( [ Atom (u i 0 `Equals` u i 1)
            | i <- [0 .. j - 1]
          ]
            <> [ Atom (u i 1 `Equals` LC.Const zero)
                   `And` Atom ((u i 0 `LC.Plus` LC.Const one) `Equals` bound i)
                 | i <- [j + 1 .. lastU]
               ]
        )

    bound :: UniQIndex -> LC.Term
    bound i =
      case ( x
               ^. #formula . #quantifiers
                 . #universalQuantifiers
           )
        !? unUniQIndex i of
        Just q -> sigma11TermToLogicConstraintTerm layout (q ^. #bound)
        Nothing ->
          die "universalTableConstraints: bound index out of range (this is a compiler bug)"

    lastRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout
          ^. #fixedColumns
            . #lastRowIndicator
            . #unLastRowIndicatorColumnIndex
