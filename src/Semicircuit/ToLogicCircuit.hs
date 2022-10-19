{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import Data.List.Extra ((!?), foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (pack)
import Halo2.FiniteField (fieldMax)
import Halo2.Polynomial (var, var', constant, plus, times)
import Halo2.Types.Circuit (Circuit (..), LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType (Fixed, Advice, Instance))
import Halo2.Types.ColumnTypes (ColumnTypes (..))
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns (..))
import Halo2.Types.EqualityConstraint (EqualityConstraint (..))
import Halo2.Types.EqualityConstraints (EqualityConstraints (..))
import Halo2.Types.FieldElement (FieldElement (..))
import Halo2.Types.LogicConstraint (LogicConstraint (Bottom, Top, Atom, And, Or, Not, Iff), AtomicLogicConstraint (LessThan, Equals))
import Halo2.Types.LogicConstraints (LogicConstraints (..))
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.FiniteField (FiniteField)
import Halo2.Types.FixedColumn (FixedColumn (..))
import Halo2.Types.FixedValues (FixedValues (..))
import Halo2.Types.RowCount (RowCount (..))
import Halo2.Types.RowIndex (RowIndex (..))
import Die (die)
import Semicircuit.Sigma11 (existentialQuantifierName, existentialQuantifierOutputBound, existentialQuantifierInputBounds)
import Semicircuit.Types.PNFFormula (UniversalQuantifier, ExistentialQuantifier (Some, SomeP))
import qualified Semicircuit.Types.QFFormula as QF
import Semicircuit.Types.Semicircuit (Semicircuit, IndicatorFunctionCall (..))
import Semicircuit.Types.SemicircuitToLogicCircuitColumnLayout (SemicircuitToLogicCircuitColumnLayout (..), NameMapping (NameMapping), OutputMapping (..), TermMapping (..), DummyRowAdviceColumn (..), FixedColumns (..), ArgMapping (..), ZeroVectorIndex (..), OneVectorIndex (..), LastRowIndicatorColumnIndex (..))
import Semicircuit.Types.Sigma11 (Name, Term (App, AppInverse, Add, Mul, IndLess, Const), Bound (TermBound, FieldMaxBound))

type Layout = SemicircuitToLogicCircuitColumnLayout

-- TODO: fixed bounds
semicircuitToLogicCircuit
  :: FiniteField
  -> RowCount
  -> Semicircuit
  -> LogicCircuit
semicircuitToLogicCircuit ff rowCount x =
  let layout = columnLayout x in
  Circuit ff
  (layout ^. #columnTypes)
  (equalityConstrainableColumns x layout)
  (gateConstraints ff x layout)
  (lookupArguments x layout)
  rowCount
  (equalityConstraints x layout)
  (fixedValues rowCount layout)


newtype S = S (ColumnIndex, ColumnTypes)


nextCol :: ColumnType -> State S ColumnIndex
nextCol t = do
  S (x, ts) <- get
  put $ S (x+1, (ts <> ColumnTypes (Map.singleton x t)))
  pure x


columnLayout :: Semicircuit -> Layout
columnLayout x =
  flip evalState (S (0, mempty)) $ do
    nm <- nameMappings x
    tm <- termMappings x
    dr <- DummyRowAdviceColumn <$> nextCol Advice
    fs <- fixedColumns
    S (_, colTypes) <- get
    pure $
      SemicircuitToLogicCircuitColumnLayout colTypes
      nm tm fs dr


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
    <$> (NameMapping <$> (OutputMapping <$> nextCol Advice)
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
          <$> (OutputMapping <$> nextCol Advice)
          <*> replicateM (x ^. #arity . #unArity)
                (ArgMapping <$> nextCol Advice))
    SomeP x _ _ _ ->
      (x,) <$>
        (NameMapping
          <$> (OutputMapping <$> nextCol Advice)
          <*> (((:[]) . ArgMapping) <$> nextCol Advice))


freeVariableMappings :: Semicircuit -> State S (Map Name NameMapping)
freeVariableMappings x =
  Map.fromList <$> sequence
  (freeVariableMapping <$>
    Set.toList (x ^. #freeVariables . #unFreeVariables))


freeVariableMapping :: Name -> State S (Name, NameMapping)
freeVariableMapping x =
  (x,) <$>
    (NameMapping
      <$> (OutputMapping <$> nextCol Instance)
      <*> (replicateM (x ^. #arity . #unArity)
            (ArgMapping <$> nextCol Instance)))


termMappings :: Semicircuit -> State S (Map Term TermMapping)
termMappings x =
  Map.fromList <$> sequence
  (termMapping <$>
    Set.toList (x ^. #adviceTerms . #unAdviceTerms))


termMapping :: Term -> State S (Term, TermMapping)
termMapping t = (t,) . TermMapping <$> nextCol Advice


fixedColumns :: State S FixedColumns
fixedColumns =
  FixedColumns
    <$> (ZeroVectorIndex <$> nextCol Fixed)
    <*> (OneVectorIndex <$> nextCol Fixed)
    <*> (LastRowIndicatorColumnIndex <$> nextCol Fixed)


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
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
gateConstraints ff x layout =
  mconcat
  [ instanceFunctionTablesDefineFunctionsConstraints x layout
  , existentialFunctionTablesDefineFunctionsConstraints x layout
  , quantifierFreeFormulaIsTrueConstraints ff x layout
  , dummyRowIndicatorConstraints ff x layout
  , lessThanIndicatorFunctionCallConstraints ff x layout
  , existentialOutputsInBoundsConstraints ff x layout
  , existentialInputsInBoundsConstraints ff x layout
  , universalTableConstraints ff x layout
  , existentialOutputIndependenceFromUniversalsConstraints x layout
  ]


lexicographicallyLessThanConstraint
     -- the lists are zipped to document that they have
     -- equal lengths
  :: [(PolynomialVariable, PolynomialVariable)]
  -> LogicConstraint
lexicographicallyLessThanConstraint ab =
  case ab of
    [] -> Bottom
    ((a,b):ab') ->
      Atom (var a `LessThan` var b)
      `Or` (Atom (var a `Equals` var b)
        `And` rec ab')
  where
    rec = lexicographicallyLessThanConstraint


equalsConstraint
  :: [(PolynomialVariable, PolynomialVariable)]
  -> LogicConstraint
equalsConstraint ab =
  case ab of
    [] -> Top
    ((a,b) : ab') ->
      Atom (var a `Equals` var b) `And` rec ab'
  where
    rec = equalsConstraint


instanceFunctionTablesDefineFunctionsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
instanceFunctionTablesDefineFunctionsConstraints x layout =
  LogicConstraints
    [ Atom (lastRowIndicator `Equals` constant 1)
      `Or` nextRowIsEqualConstraint layout v
      `Or` nextInputRowIsLexicographicallyGreaterConstraint layout v
    | v <- Set.toList (x ^. #freeVariables . #unFreeVariables)
    ]
    mempty
  where
    lastRowIndicator = var'
      $ layout ^. #fixedColumns
      . #lastRowIndicator
      . #unLastRowIndicatorColumnIndex


nextRowIsEqualConstraint
  :: Layout
  -> Name
  -> LogicConstraint
nextRowIsEqualConstraint layout v =
  equalsConstraint (zip (vars 0) (vars 1))
  where
    vars :: RowIndex -> [PolynomialVariable]
    vars i =
      case Map.lookup v (layout ^. #nameMappings) of
        Just nm -> (PolynomialVariable
                     (nm ^. #outputMapping . #unOutputMapping)
                     i :)
                 $ (\c -> PolynomialVariable c i)
                 . (^. #unArgMapping)
               <$> (nm ^. #argMappings)
        Nothing -> die "nextRowIsEqualConstraint: failed lookup (this is a compiler bug)"


nextInputRowIsLexicographicallyGreaterConstraint
  :: Layout
  -> Name
  -> LogicConstraint
nextInputRowIsLexicographicallyGreaterConstraint layout v =
  lexicographicallyLessThanConstraint
  (zip (vars 0) (vars 1))
  where
    vars :: RowIndex -> [PolynomialVariable]
    vars i =
      case Map.lookup v (layout ^. #nameMappings) of
        Just nm -> (\c -> PolynomialVariable c i)
                 . (^. #unArgMapping)
               <$> (nm ^. #argMappings)
        Nothing -> die "nextInputRowIsLexicographicallyGreaterConstraint: failed lookup (this is a compiler bug)"


existentialFunctionTablesDefineFunctionsConstraints
  :: Semicircuit
  -> Layout
  -> LogicConstraints
existentialFunctionTablesDefineFunctionsConstraints x layout =
  LogicConstraints
    [ Atom (lastRowIndicator `Equals` constant 1)
      `Or` nextRowIsEqualConstraint layout v
      `Or` nextInputRowIsLexicographicallyGreaterConstraint layout v
    | v <- existentialQuantifierName
        <$> x ^. #formula . #quantifiers . #existentialQuantifiers
    ]
    mempty
  where
    lastRowIndicator = var'
      $ layout ^. #fixedColumns
      . #lastRowIndicator
      . #unLastRowIndicatorColumnIndex


termToPolynomial
  :: FiniteField
  -> Layout
  -> Term
  -> Polynomial
termToPolynomial ff layout =
  \case
    App x [] ->
      case Map.lookup x names of
        Just (NameMapping (OutputMapping o) []) ->
          var' o
        Just (NameMapping _ _) -> die "termToPolynomial: encountered empty application with non-empty name mapping (this is a compiler bug)"
        Nothing -> die "termToPolynomial: failed name mapping lookup (this is a compiler bug)"
    t@(App {}) -> lookupTerm t
    t@(AppInverse {}) -> lookupTerm t
    Add x y -> plus ff (rec x) (rec y)
    Mul x y -> times ff (rec x) (rec y)
    t@(IndLess {}) -> lookupTerm t
    Const x ->
      if x < ff ^. #order
      then constant (FieldElement x)
      else die $ "in termToPolynomial: constant term " <> pack (show x) <> " is greater than or equal to the field order " <> pack (show (ff ^. #order)) <> " (this is a compiler bug; should have been caught earlier)"
  where
    rec = termToPolynomial ff layout

    names :: Map Name NameMapping
    names = layout ^. #nameMappings

    terms :: Map Term TermMapping
    terms = layout ^. #termMappings

    lookupTerm :: Term -> Polynomial
    lookupTerm t =
      case Map.lookup t terms of
        Just (TermMapping i) -> var' i
        Nothing -> die "termToPolynomial: failed term mapping lookup (this is a compiler bug)"


qfFormulaToLogicConstraint
  :: FiniteField
  -> Layout
  -> QF.Formula
  -> LogicConstraint
qfFormulaToLogicConstraint ff layout =
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
  where
    rec = qfFormulaToLogicConstraint ff layout
    term = termToPolynomial ff layout


quantifierFreeFormulaIsTrueConstraints
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
quantifierFreeFormulaIsTrueConstraints ff x layout =
  LogicConstraints
  [ Atom (dummyRowIndicator `Equals` constant 1)
    `Or` qfFormulaToLogicConstraint ff layout
         (x ^. #formula . #qfFormula)
  ]
  mempty
  where
    dummyRowIndicator =
      var' $ layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn


dummyRowIndicatorConstraints
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
dummyRowIndicatorConstraints ff x layout =
  LogicConstraints
  [ Atom (dummyRowIndicator `Equals` constant 0)
    `Or` Atom (dummyRowIndicator `Equals` constant 1)
  , Atom (dummyRowIndicator `Equals` constant 0)
    `Iff` someUniversalQuantifierBoundIsZeroConstraint ff x layout
  ]
  mempty
  where
    dummyRowIndicator =
      var' $ layout ^. #dummyRowAdviceColumn . #unDummyRowAdviceColumn


someUniversalQuantifierBoundIsZeroConstraint
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraint
someUniversalQuantifierBoundIsZeroConstraint ff x layout =
  let boundPolys = universalQuantifierBoundPolynomials ff x layout
  in foldl Or Top
     [ Atom (p `Equals` constant 0) | p <- boundPolys ]


universalQuantifierBoundPolynomials
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> [Polynomial]
universalQuantifierBoundPolynomials ff x layout =
  let bounds = (^. #bound) <$> x ^. #formula . #quantifiers
               . #universalQuantifiers
  in boundPolynomial ff layout <$> bounds


boundPolynomial
  :: FiniteField
  -> Layout
  -> Bound
  -> Polynomial
boundPolynomial ff layout =
  \case
    TermBound x -> termToPolynomial ff layout x
    FieldMaxBound -> constant (fieldMax ff)


lessThanIndicatorFunctionCallConstraints
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
lessThanIndicatorFunctionCallConstraints ff x layout =
  LogicConstraints
  [ (Atom (a `Equals` constant 0) `Or` Atom (a `Equals` constant 1))
    `And` (Atom (a `Equals` constant 1) `Iff`
           Atom (term y `Equals` term z))
  | IndicatorFunctionCall y z <-
      Set.toList (x ^. #indicatorCalls . #unIndicatorFunctionCalls)
  , let a = case Map.lookup (IndLess y z)
                 (layout ^. #termMappings) of
              Just (TermMapping c) -> var' c
              Nothing -> die "lessThanIndicatorFunctionCallConstraints: lookup failed (this is a compiler bug)"
  ]
  mempty
  where
    term = termToPolynomial ff layout


existentialOutputsInBoundsConstraints
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
existentialOutputsInBoundsConstraints ff x layout =
  LogicConstraints
  [ Atom (LessThan y bp)
  | q <- x ^. #formula . #quantifiers
            . #existentialQuantifiers
  , let bp = boundPolynomial ff layout 
           $ existentialQuantifierOutputBound q
  , let y  = mapName $ existentialQuantifierName q
  ]
  mempty
  where
    mapName :: Name -> Polynomial
    mapName y =
      case Map.lookup y (layout ^. #nameMappings) of
        Just nm -> var' (nm ^. #outputMapping . #unOutputMapping)
        Nothing -> die "existentialOutputsInBoundsConstraints: lookup failed (this is a compiler bug)"


existentialInputsInBoundsConstraints
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
existentialInputsInBoundsConstraints ff x layout =
  LogicConstraints
  [ Atom (LessThan y bp)
  | q <- x ^. #formula . #quantifiers
            . #existentialQuantifiers
  , (i, ib) <- zip [0..] (existentialQuantifierInputBounds q)
  , let bp = boundPolynomial ff layout (ib ^. #bound)
  , let y  = name (existentialQuantifierName q) i
  ]
  mempty
  where
    name :: Name -> Int -> Polynomial
    name n i =
      case Map.lookup n (layout ^. #nameMappings) of
        Just nm ->
          case (nm ^. #argMappings) !? i of
            Just (ArgMapping j) -> var' j
            Nothing -> die "existentialInputsInBoundsConstraints: failed arg mapping lookup (this is a compiler bug)"
        Nothing -> die "existentialInputsInBoundsConstraints: failed name lookup (this is a compiler bug)"


newtype UniQIndex = UniQIndex { unUniQIndex :: Int }
  deriving (Eq, Ord, Num, Enum)


universalTableConstraints
  :: FiniteField
  -> Semicircuit
  -> Layout
  -> LogicConstraints
universalTableConstraints ff x layout =
  LogicConstraints
  [ foldl' Or
    (Atom (lastRowIndicator `Equals` constant 1)
       `Or` next lastU)
    [ foldl' And
      (Atom (bound i `Equals` constant 0)
        `And` next (i-1))
      [ Atom (u j 0 `Equals` constant 0) -- TODO is this needed?
          `And` Atom (u j 1 `Equals` constant 0)
      | j <- [i..lastU]
      ]
    | i <- [0..lastU]
    ]
  ]
  mempty
  where
    lastU :: UniQIndex
    lastU = UniQIndex
          $ length (x ^. #formula . #quantifiers
                       . #universalQuantifiers)
              - 1

    u :: UniQIndex -> RowIndex -> Polynomial
    u i j =
      case (x ^. #formula . #quantifiers
               . #universalQuantifiers)
           !? unUniQIndex i of
        Just q ->
          case Map.lookup (q ^. #name)
                          (layout ^. #nameMappings) of
            Just nm ->
              var $
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
      (
        foldl' And
          (Atom (plus ff (u j 0) (constant 1) `Equals` u j 1))
          [ Atom (u i 0 `Equals` u i 1)
          | i <- [0..j-2]
          ]
      ) `Or` (
        Atom (plus ff (u j 0) (constant 1) `Equals` bound j)
        `And` Atom (u j 1 `Equals` constant 0)
        `And` next (j-1)
      )

    bound :: UniQIndex -> Polynomial
    bound i =
      case (x ^. #formula . #quantifiers
               . #universalQuantifiers)
           !? unUniQIndex i of
        Just q -> boundPolynomial ff layout (q ^. #bound)
        Nothing ->
          die "universalTableConstraints: bound index out of range (this is a compiler bug)"


    lastRowIndicator = var' $ layout ^. #fixedColumns
      . #lastRowIndicator . #unLastRowIndicatorColumnIndex


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
