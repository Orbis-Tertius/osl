{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Semicircuit.ToLogicCircuit
  ( semicircuitToLogicCircuit,
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
    lookupArguments,
  )
where

import Cast (word64ToInteger)
import Control.Lens ((<&>), (^.))
import Control.Monad (replicateM)
import Control.Monad.State (State, evalState, get, put)
import Data.List.Extra (foldl', (!?))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (Text, pack)
import Die (die)
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
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top))
import qualified Halo2.Types.LogicConstraint as LC
import Halo2.Types.LogicConstraints (LogicConstraints (..))
import Halo2.Types.LookupArgument (LookupArgument (..))
import Halo2.Types.LookupArguments (LookupArguments (..))
import Halo2.Types.LookupTableColumn (LookupTableColumn (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.RowCount (RowCount (..))
import Halo2.Types.RowIndex (RowIndex (..), RowIndexType (Relative))
import Semicircuit.Sigma11 (existentialQuantifierInputBounds, existentialQuantifierName, existentialQuantifierOutputBound)
import Semicircuit.Types.PNFFormula (ExistentialQuantifier (Some, SomeP), InstanceQuantifier (Instance), UniversalQuantifier (All))
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Semicircuit (FunctionCall (..), Semicircuit)
import Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout (ArgMapping (..), DummyRowAdviceColumn (..), FixedColumns (..), LastRowIndicatorColumnIndex (..), NameMapping (NameMapping), OneVectorIndex (..), OutputMapping (..), SemicircuitToLogicCircuitColumnLayout (..), TermMapping (..), ZeroVectorIndex (..))
import Semicircuit.Types.Sigma11 (Bound (FieldMaxBound, TermBound), InputBound, Name, OutputBound (OutputBound), Term (Add, App, AppInverse, Const, IndLess, Max, Mul))
import Stark.Types.Scalar (minusOne, one, order, scalarToInt, zero)

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
          (columnBounds x layout (gateConstraints x layout))
          (lookupArguments x layout)
          rowCount
          (equalityConstraints x layout)
          (fixedValues rowCount layout),
        layout
      )

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
    tm <- termMappings x
    dr <- DummyRowAdviceColumn <$> nextCol ColType.Advice
    fs <- fixedColumns
    S (_, colTypes) <- get
    pure $
      SemicircuitToLogicCircuitColumnLayout
        colTypes
        nm
        tm
        fs
        dr

nameMappings :: Semicircuit -> State S (Map Name NameMapping)
nameMappings x =
  mconcat
    <$> sequence
      [ freeVariableMappings x,
        instanceVariableMappings x,
        universalVariableMappings x,
        existentialVariableMappings x
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

instanceVariableMappings :: Semicircuit -> State S (Map Name NameMapping)
instanceVariableMappings x =
  Map.fromList
    <$> mapM
      instanceVariableMapping
      (x ^. #formula . #quantifiers . #instanceQuantifiers)

instanceVariableMapping ::
  InstanceQuantifier ->
  State S (Name, NameMapping)
instanceVariableMapping q =
  (q ^. #name,)
    <$> ( NameMapping
            <$> (OutputMapping <$> nextCol ColType.Instance)
            <*> replicateM
              (q ^. #name . #arity . #unArity)
              (ArgMapping <$> nextCol ColType.Instance)
        )

existentialVariableMappings ::
  Semicircuit ->
  State S (Map Name NameMapping)
existentialVariableMappings x =
  Map.fromList
    <$> mapM
      existentialVariableMapping
      (x ^. #formula . #quantifiers . #existentialQuantifiers)

existentialVariableMapping ::
  ExistentialQuantifier -> State S (Name, NameMapping)
existentialVariableMapping =
  \case
    Some x _ _ _ ->
      (x,)
        <$> ( NameMapping
                <$> (OutputMapping <$> nextCol ColType.Advice)
                <*> replicateM
                  (x ^. #arity . #unArity)
                  (ArgMapping <$> nextCol ColType.Advice)
            )
    SomeP x _ _ _ ->
      (x,)
        <$> ( NameMapping
                <$> (OutputMapping <$> nextCol ColType.Advice)
                <*> ((: []) . ArgMapping <$> nextCol ColType.Advice)
            )

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

termMappings :: Semicircuit -> State S (Map Term TermMapping)
termMappings x =
  Map.fromList
    <$> mapM
      termMapping
      (Set.toList (x ^. #adviceTerms . #unAdviceTerms))

termMapping :: Term -> State S (Term, TermMapping)
termMapping t = (t,) . TermMapping <$> nextCol ColType.Advice

fixedColumns :: State S FixedColumns
fixedColumns =
  FixedColumns
    <$> (ZeroVectorIndex <$> nextCol ColType.Fixed)
    <*> (OneVectorIndex <$> nextCol ColType.Fixed)
    <*> (LastRowIndicatorColumnIndex <$> nextCol ColType.Fixed)

fixedValues :: RowCount -> Layout -> FixedValues
fixedValues (RowCount n) layout =
  FixedValues . Map.fromList $
    [ ( layout
          ^. #fixedColumns . #zeroVector
            . #unZeroVectorIndex,
        FixedColumn $ replicate (scalarToInt n) zero
      ),
      ( layout
          ^. #fixedColumns . #oneVector
            . #unOneVectorIndex,
        FixedColumn $ replicate (scalarToInt n) one
      ),
      ( layout
          ^. #fixedColumns . #lastRowIndicator
            . #unLastRowIndicatorColumnIndex,
        FixedColumn $ replicate (scalarToInt n - 1) zero <> [one]
      )
    ]

equalityConstraints ::
  Semicircuit ->
  Layout ->
  EqualityConstraints
equalityConstraints x layout =
  EqualityConstraints
    [ EqualityConstraint $
        [ CellReference
            ( layout
                ^. #fixedColumns . #zeroVector
                  . #unZeroVectorIndex
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
        ^. #fixedColumns . #zeroVector
          . #unZeroVectorIndex
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
  functionCallOutputColumnBounds x layout
    . adviceTermColumnBounds x layout
    . dummyRowAdviceColumnBounds layout
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
  quantifierBounds "universal" x layout name [] (OutputBound bound)

functionCallOutputColumnBounds ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  LogicConstraints
functionCallOutputColumnBounds x layout =
  foldl'
    (.)
    id
    ( functionCallOutputColumnBound layout
        <$> Set.toList (x ^. #functionCalls . #unFunctionCalls)
    )

functionCallOutputColumnBound ::
  Layout ->
  FunctionCall ->
  LogicConstraints ->
  LogicConstraints
functionCallOutputColumnBound layout (FunctionCall name _) constraints =
  case Map.lookup name (layout ^. #nameMappings) of
    Just (NameMapping (OutputMapping i) _) ->
      case Map.lookup i (constraints ^. #bounds) of
        Just b ->
          constraints <> LogicConstraints mempty (Map.singleton i b)
        Nothing ->
          die $
            "functionCallOutputColumnBound: output bound lookup failed (this is a compiler bug)"
              <> pack (show (name, i, constraints ^. #bounds))
    Nothing -> die "functionCallOutputColumnBound: name mapping lookup failed (this is a compiler bug)"

adviceTermColumnBounds ::
  Semicircuit ->
  Layout ->
  LogicConstraints ->
  LogicConstraints
adviceTermColumnBounds x layout constraints =
  constraints
    <> mconcat
      [ LogicConstraints
          mempty
          (Map.singleton i (termToFixedBound x layout constraints term))
        | (term, TermMapping i) <- Map.toList (layout ^. #termMappings)
      ]

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
          [ (layout ^. #fixedColumns . #lastRowIndicator . #unLastRowIndicatorColumnIndex, boolBound),
            (layout ^. #fixedColumns . #oneVector . #unOneVectorIndex, boolBound),
            (layout ^. #fixedColumns . #zeroVector . #unZeroVectorIndex, boolBound)
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
    [ Atom (lastRowIndicator `Equals` LC.Const one)
        `Or` nextRowIsEqualConstraint layout v
        `Or` nextInputRowIsLexicographicallyGreaterConstraint layout v
      | v <- Set.toList (x ^. #freeVariables . #unFreeVariables)
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
    [ Atom (lastRowIndicator `Equals` LC.Const one)
        `Or` nextRowIsEqualConstraint layout v
        `Or` nextInputRowIsLexicographicallyGreaterConstraint layout v
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
        Just (NameMapping _ _) -> die "termToPolynomial: encountered empty application with non-empty name mapping (this is a compiler bug)"
        Nothing -> die $ "termToPolynomial: failed name mapping lookup (this is a compiler bug)\n" <> pack (show x)
    t@(App {}) -> lookupTerm t
    t@(AppInverse {}) -> lookupTerm t
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

    terms :: Map Term TermMapping
    terms = layout ^. #termMappings

    lookupTerm :: Term -> LC.Term
    lookupTerm t =
      case Map.lookup t terms of
        Just (TermMapping i) -> LC.Var (PolynomialVariable i 0)
        Nothing -> die $ "termToPolynomial: failed term mapping lookup (this is a compiler bug)\n" <> pack (show t)

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
    [ Atom (dummyRowIndicator `Equals` LC.Const one)
        `Or` qfFormulaToLogicConstraint
          layout
          (x ^. #formula . #qfFormula)
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
    [ Atom (dummyRowIndicator `Equals` LC.Const zero)
        `Or` Atom (dummyRowIndicator `Equals` LC.Const one),
      Atom (dummyRowIndicator `Equals` LC.Const zero)
        `Iff` someUniversalQuantifierBoundIsZeroConstraint x layout
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
  let bounds =
        (^. #bound) <$> x
          ^. #formula . #quantifiers
            . #universalQuantifiers
   in boundTerm layout <$> bounds

boundTerm ::
  Layout ->
  Bound ->
  LC.Term
boundTerm layout =
  \case
    TermBound x -> sigma11TermToLogicConstraintTerm layout x
    FieldMaxBound -> LC.Const maxBound

-- lessThanIndicatorFunctionCallConstraints ::
--   Semicircuit ->
--   Layout ->
--   LogicConstraints
-- lessThanIndicatorFunctionCallConstraints x layout =
--   LogicConstraints
--     [ (Atom (a `Equals` constant 0) `Or` Atom (a `Equals` constant 1))
--         `And` ( Atom (a `Equals` constant 1)
--                   `Iff` Atom (term y `Equals` term z)
--               )
--       | IndicatorFunctionCall y z <-
--           Set.toList (x ^. #indicatorCalls . #unIndicatorFunctionCalls),
--         let a = case Map.lookup
--               (IndLess y z)
--               (layout ^. #termMappings) of
--               Just (TermMapping c) -> var' c
--               Nothing -> die "lessThanIndicatorFunctionCallConstraints: lookup failed (this is a compiler bug)"
--     ]
--     mempty
--   where
--     term = termToPolynomial layout

existentialOutputsInBoundsConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
existentialOutputsInBoundsConstraints x layout =
  LogicConstraints
    [ Atom (LessThan y bp)
      | q <-
          x
            ^. #formula . #quantifiers
              . #existentialQuantifiers,
        let bp =
              boundTerm layout $
                existentialQuantifierOutputBound q,
        let y = mapName $ existentialQuantifierName q
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
    [ Atom (LessThan y bp)
      | q <-
          x
            ^. #formula . #quantifiers
              . #existentialQuantifiers,
        (i, ib) <- zip [0 ..] (existentialQuantifierInputBounds q),
        let bp = boundTerm layout (ib ^. #bound),
        let y = name (existentialQuantifierName q) i
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
  deriving (Eq, Ord, Num, Enum)

universalTableConstraints ::
  Semicircuit ->
  Layout ->
  LogicConstraints
universalTableConstraints x layout =
  LogicConstraints
    [ foldl'
        Or
        ( Atom (lastRowIndicator `Equals` LC.Const one)
            `Or` next lastU
        )
        [ foldl'
            And
            ( Atom (bound i `Equals` LC.Const zero)
                `And` next (i - 1)
            )
            [ Atom (u j 0 `Equals` LC.Const zero) -- TODO is this needed?
                `And` Atom (u j 1 `Equals` LC.Const zero)
              | j <- [i .. lastU]
            ]
          | i <- [0 .. lastU]
        ]
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

    next :: UniQIndex -> LogicConstraint
    next (-1) = Top
    next 0 = Atom (u 1 0 `Equals` u 1 1)
    next j =
      ( foldl'
          And
          (Atom ((u j 0 `LC.Plus` LC.Const zero) `Equals` u j 1))
          [ Atom (u i 0 `Equals` u i 1)
            | i <- [0 .. j - 2]
          ]
      )
        `Or` ( Atom ((u j 0 `LC.Plus` LC.Const one) `Equals` bound j)
                 `And` Atom (u j 1 `Equals` LC.Const zero)
                 `And` next (j - 1)
             )

    bound :: UniQIndex -> LC.Term
    bound i =
      case ( x
               ^. #formula . #quantifiers
                 . #universalQuantifiers
           )
        !? unUniQIndex i of
        Just q -> boundTerm layout (q ^. #bound)
        Nothing ->
          die "universalTableConstraints: bound index out of range (this is a compiler bug)"

    lastRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout
          ^. #fixedColumns
            . #lastRowIndicator
            . #unLastRowIndicatorColumnIndex

lookupArguments ::
  Semicircuit ->
  Layout ->
  LookupArguments LC.Term
lookupArguments = functionCallLookupArguments

newtype FunctionIndex = FunctionIndex Int
  deriving (Eq, Ord, Num)

newtype FunctionCallIndex = FunctionCallIndex Int

newtype ArgumentIndex = ArgumentIndex Int

functionCallLookupArguments ::
  Semicircuit ->
  Layout ->
  LookupArguments LC.Term
functionCallLookupArguments x layout =
  LookupArguments
    [ LookupArgument
        (dummyRowIndicator `LC.Plus` LC.Const minusOne)
        ( [(outputEval i j, outputColumn i)]
            <> [ (argEval i j k, inputColumn i k)
                 | k <- argumentIndices i
               ]
        )
      | i <- functionIndices,
        j <- functionCallIndices i
    ]
  where
    functionSymbols :: [Name]
    functionSymbols =
      filter ((> 0) . (^. #arity))
        . Map.keys
        $ layout ^. #nameMappings

    functionSymbol :: FunctionIndex -> Name
    functionSymbol (FunctionIndex i) =
      fromMaybe
        (die "functionCallLookupArguments: functionSymbol: lookup failed (this is a compiler bug)")
        (functionSymbols !? i)

    functionIndices :: [FunctionIndex]
    functionIndices =
      FunctionIndex <$> [0 .. length functionSymbols - 1]

    functionCalls :: FunctionIndex -> [FunctionCall]
    functionCalls i =
      filter
        ((== functionSymbol i) . (^. #name))
        (Set.toList (x ^. #functionCalls . #unFunctionCalls))

    functionCall :: FunctionIndex -> FunctionCallIndex -> FunctionCall
    functionCall i (FunctionCallIndex j) =
      fromMaybe (die "functionCallLookupArguments: functionCall: call index out of range (this is a compiler bug") $
        functionCalls i !? j

    functionCallIndices :: FunctionIndex -> [FunctionCallIndex]
    functionCallIndices i = FunctionCallIndex <$> [0 .. length (functionCalls i) - 1]

    argumentIndices :: FunctionIndex -> [ArgumentIndex]
    argumentIndices i = ArgumentIndex <$> [0 .. functionSymbol i ^. #arity . #unArity - 1]

    functionCallArgument :: FunctionIndex -> FunctionCallIndex -> ArgumentIndex -> Term
    functionCallArgument i j (ArgumentIndex k) =
      fromMaybe
        ( die $
            "functionCallLookupArguments: functionCallArgument: argument index out of range (this is a compiler bug)\n"
              <> pack (show (functionSymbol i, functionCall i j, k))
        )
        $ NonEmpty.toList (functionCall i j ^. #args) !? k

    outputEval :: FunctionIndex -> FunctionCallIndex -> InputExpression LC.Term
    outputEval i j =
      InputExpression . LC.Var . flip PolynomialVariable 0 . (^. #unTermMapping)
        . fromMaybe (die "functionCallLookupArguments: outputEval: term mapping lookup failed (this is a compiler bug)")
        $ Map.lookup t (layout ^. #termMappings)
      where
        FunctionCall f xs = functionCall i j
        t = App f (NonEmpty.toList xs)

    argEval :: FunctionIndex -> FunctionCallIndex -> ArgumentIndex -> InputExpression LC.Term
    argEval i j k =
      InputExpression
        . sigma11TermToLogicConstraintTerm layout
        $ functionCallArgument i j k

    outputColumn :: FunctionIndex -> LookupTableColumn
    outputColumn i =
      case Map.lookup (functionSymbol i) (layout ^. #nameMappings) of
        Just nm ->
          LookupTableColumn $ nm ^. #outputMapping . #unOutputMapping
        Nothing -> die "functionCallLookupArguments: outputColumn: lookup failed (this is a compiler bug)"

    inputColumn :: FunctionIndex -> ArgumentIndex -> LookupTableColumn
    inputColumn i (ArgumentIndex k) =
      case Map.lookup (functionSymbol i) (layout ^. #nameMappings) of
        Just nm ->
          maybe
            (die "functionCallLookupArguments: inputColumn: argument index out of range (this is a compiler bug")
            (LookupTableColumn . (^. #unArgMapping))
            ((nm ^. #argMappings) !? k)
        Nothing -> die "functionCallLookupArguments: inputColumn: name lookup failed (this is a compiler bug)"

    dummyRowIndicator =
      LC.Var . flip PolynomialVariable 0 $
        layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn
