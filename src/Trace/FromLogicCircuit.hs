{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Trace.FromLogicCircuit
  ( logicCircuitToTraceType,
    argumentToTrace,
    getMapping,
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger, integerToInt)
import Control.Applicative ((<|>))
import Control.Lens ((<&>), _1, _3)
import Control.Monad (foldM, mzero, replicateM, when)
import Control.Monad.Trans.State (State, evalState, get, put)
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import Die (die)
import Halo2.ByteDecomposition (countBytes, decomposeBytes)
import Halo2.Circuit (getLookupArguments, getLookupTables, getPolynomialVariables, getScalars, lessIndicator)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import qualified Halo2.Types.Argument as LC
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Advice))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.FixedColumn (FixedColumn (FixedColumn))
import Halo2.Types.FixedValues (FixedValues (FixedValues))
import Halo2.Types.InputExpression (InputExpression (InputExpression))
import Halo2.Types.Label (Label (Label))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint, LogicConstraint)
import qualified Halo2.Types.LogicConstraint as LC
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (..))
import Halo2.Types.PolynomialDegreeBound (PolynomialDegreeBound (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.RowCount (RowCount (RowCount))
import Halo2.Types.RowIndex (RowIndex (RowIndex))
import Halo2.Types.Sign (Sign (Positive, Negative))
import OSL.Types.Arity (Arity (Arity))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Stark.Types.Scalar (Scalar, integerToScalar, one, two, zero, scalarToInteger)
import Trace.Types (CaseNumberColumnIndex (..), InputColumnIndex (..), InputSubexpressionId (..), NumberOfCases (NumberOfCases), OutputColumnIndex (..), OutputSubexpressionId (..), ResultExpressionId (ResultExpressionId), StepIndicatorColumnIndex (..), StepType (StepType), StepTypeColumnIndex (..), StepTypeId (StepTypeId), SubexpressionId (SubexpressionId), SubexpressionLink (..), TraceType (TraceType), Trace (Trace), Case (Case), Statement (Statement), Witness (Witness), SubexpressionTrace (SubexpressionTrace))

data LookupCaches =
  LookupCaches
    { lookupTermCaches ::
        Map (Set LookupTableColumn, LC.LookupTableOutputColumn)
          (Map (Map LookupTableColumn Scalar) Scalar),
      lookupArgumentCaches ::
        Map (Set LookupTableColumn)
          (Set (Map LookupTableColumn Scalar))
    }
  deriving Generic

getLookupCaches ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Either (ErrorMessage ann) LookupCaches
getLookupCaches = todo

argumentToTrace ::
  ann ->
  BitsPerByte ->
  LogicCircuit ->
  LC.Argument ->
  Either (ErrorMessage ann) Trace
argumentToTrace ann bitsPerByte lc arg = do
  usedCases <- logicCircuitUsedCases ann lc
  Trace
    <$> logicCircuitStatementToTraceStatement ann (arg ^. #statement)
    <*> logicCircuitWitnessToTraceWitness ann (arg ^. #witness)
    <*> pure usedCases
    <*> argumentSubexpressionTraces ann bitsPerByte lc arg usedCases

logicCircuitUsedCases ::
  ann ->
  LogicCircuit ->
  Either (ErrorMessage ann) (Set Case)
logicCircuitUsedCases ann lc =
  Set.fromList <$> sequence
    [ maybe (Left (ErrorMessage ann "case index outside of scalar field"))
        (pure . Case) (integerToScalar i)
      | i <- [0 .. scalarToInteger (lc ^. #rowCount . #getRowCount)]
    ]

argumentSubexpressionTraces ::
  ann ->
  BitsPerByte ->
  LogicCircuit ->
  LC.Argument ->
  Set Case ->
  Either (ErrorMessage ann) (Map (Case, SubexpressionId) SubexpressionTrace)
argumentSubexpressionTraces ann bitsPerByte lc arg cases = do
  tables <- getLookupCaches ann lc arg
  mconcat <$>
    mapM (\c -> Map.mapKeys (c,) <$>
           caseArgumentSubexpressionTraces ann lc arg mapping tables c)
         (Set.toList cases)
  where
    mapping = getMapping bitsPerByte lc

caseArgumentSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace)
caseArgumentSubexpressionTraces ann lc arg mapping tables c =
  (<>)
    <$> (mconcat <$>
           mapM (fmap (^. _1) . logicConstraintSubexpressionTraces ann lc arg mapping tables c)
             ((lc ^. #gateConstraints . #constraints) <&> snd))
    <*> (mconcat <$> mapM (lookupArgumentSubexpressionTraces ann lc arg mapping tables c)
                       (Set.toList (lc ^. #lookupArguments . #getLookupArguments)))

logicConstraintSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  LogicConstraint ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace, SubexpressionId, Scalar)
logicConstraintSubexpressionTraces ann lc arg mapping tables c =
   \case
     LC.Atom (LC.Equals x y) -> do
       -- TODO: fill byte decomposition advice
       (m0, s0, x') <- term x
       (m1, s1, y') <- term y
       advice <- getByteDecomposition ann lc mapping (x' Group.- y')
       s2 <- getOperationSubexpressionId ann mapping (Equals' s0 s1)
       let v = if x' == y' then one else zero
           m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #equals . #unOf) advice)
       pure (m0 <> m1 <> m2, s2, v)
     LC.Atom (LC.LessThan x y) -> do
       (m0, s0, x') <- term x
       (m1, s1, y') <- term y
       advice <- getByteDecomposition ann lc mapping (x' Group.- y')
       s2 <- getOperationSubexpressionId ann mapping (LessThan' s0 s1)
       let v = if x' < y' then one else zero
           m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #lessThan . #unOf) advice)
       pure (m0 <> m1 <> m2, s2, v)
     LC.Not p -> do
       (m0, s0, x') <- rec p
       s1 <- getOperationSubexpressionId ann mapping (Not' s0)
       let v = one Group.- x'
           m1 = Map.singleton s1 (SubexpressionTrace v (mapping ^. #stepTypeIds . #not . #unOf) defaultAdvice)
       pure (m0 <> m1, s1, v)
     LC.And p q -> do
       (m0, s0, x') <- rec p
       if x' == zero
         then do
           s1 <- getOperationSubexpressionId ann mapping (TimesAndShortCircuit' s0)
           let m1 = Map.singleton s1 (SubexpressionTrace zero (mapping ^. #stepTypeIds . #timesAndShortCircuit . #unOf) defaultAdvice)
           pure (m0 <> m1, s1, zero)
         else do
           (m1, s1, y') <- rec q
           s2 <- getOperationSubexpressionId ann mapping (TimesAnd' s0 s1)
           let v = x' Ring.* y'
               m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #timesAnd . #unOf) defaultAdvice)
           pure (m0 <> m1 <> m2, s2, v)
     LC.Or p q -> do
       (m0, s0, x') <- rec p
       if x' == one
         then do
           s1 <- getOperationSubexpressionId ann mapping (OrShortCircuit' s0)
           let m1 = Map.singleton s1 (SubexpressionTrace one (mapping ^. #stepTypeIds . #orShortCircuit . #unOf) defaultAdvice)
           pure (m0 <> m1, s1, one)
         else do
           (m1, s1, y') <- rec q
           s2 <- getOperationSubexpressionId ann mapping (Or' s0 s1)
           let v = (x' Group.+ y') Group.- (x' Ring.* y')
               m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #or . #unOf) defaultAdvice)
           pure (m0 <> m1 <> m2, s2, v)
     LC.Iff p q -> do
       (m0, s0, x') <- rec p
       (m1, s1, y') <- rec q
       s2 <- getOperationSubexpressionId ann mapping (Iff' s0 s1)
       let v = if x' == y' then one else zero
           m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #iff . #unOf) defaultAdvice)
       pure (m0 <> m1 <> m2, s2, v)
     LC.Top -> do
       sId <- getConstantSubexpressionId ann mapping one
       stId <- getConstantStepTypeId ann mapping one
       pure (Map.singleton sId (SubexpressionTrace one stId defaultAdvice), sId, one)
     LC.Bottom -> do
       sId <- getConstantSubexpressionId ann mapping zero
       stId <- getConstantStepTypeId ann mapping zero
       pure (Map.singleton sId (SubexpressionTrace zero stId defaultAdvice), sId, zero)
  where
    rec = logicConstraintSubexpressionTraces ann lc arg mapping tables c
    term = logicTermSubexpressionTraces ann lc arg mapping tables c
    defaultAdvice = getDefaultAdvice mapping

getDefaultAdvice :: Mapping -> Map ColumnIndex Scalar
getDefaultAdvice mapping =
  Map.singleton
    (mapping ^. #byteDecomposition . #sign . #unSignColumnIndex)
    zero
  <>
  mconcat
    [ Map.fromList
        [ (bc ^. #unByteColumnIndex, zero),
          (tc ^. #unTruthValueColumnIndex, zero)
        ]
      | (bc, tc) <- mapping ^. #byteDecomposition . #bytes
    ]

getByteDecomposition ::
  ann ->
  LogicCircuit ->
  Mapping ->
  Scalar ->
  Either (ErrorMessage ann) (Map ColumnIndex Scalar)
getByteDecomposition ann lc mapping x = do
  let bitsPerByte = mapping ^. #byteDecomposition . #bits
      signCol = mapping ^. #byteDecomposition . #sign
      byteCols = mapping ^. #byteDecomposition . #bytes
      expectedLength = getByteDecompositionLength bitsPerByte lc
      bytes' = decomposeBytes bitsPerByte x
      signScalar =
        case bytes' ^. #sign of
          Positive -> one
          Negative -> zero
  when (length byteCols /= expectedLength)
    (Left (ErrorMessage ann "unexpected byte decomposition mapping length"))
  when (length (bytes' ^. #bytes) /= expectedLength)
    (Left (ErrorMessage ann "unexpected byte decomposition length"))
  pure $ Map.singleton (signCol ^. #unSignColumnIndex) signScalar
    <> mconcat
         [ Map.fromList
             [ (bCol ^. #unByteColumnIndex, b),
               (tCol ^. #unTruthValueColumnIndex, t)
             ]
           | ((bCol, tCol), (b, t)) <-
               zip byteCols
                 [ (b, if b == zero then one else zero)
                   | b <- (bytes' ^. #bytes) <&> (^. #unByte)
                 ]
         ]

getOperationSubexpressionId ::
  ann ->
  Mapping ->
  Operation ->
  Either (ErrorMessage ann) SubexpressionId
getOperationSubexpressionId ann mapping op =
  case Map.lookup op (mapping ^. #subexpressionIds . #operations) of
    Just sId -> pure (sId ^. #unOf)
    Nothing -> Left (ErrorMessage ann "operation subexpression id not found")

getConstantStepTypeId ::
  ann ->
  Mapping ->
  Scalar ->
  Either (ErrorMessage ann) StepTypeId
getConstantStepTypeId ann mapping x =
  case Map.lookup x (mapping ^. #stepTypeIds . #constants) of
    Just sId -> pure sId
    Nothing -> Left (ErrorMessage ann "constant step type id not found")

getConstantSubexpressionId ::
  ann ->
  Mapping ->
  Scalar ->
  Either (ErrorMessage ann) SubexpressionId
getConstantSubexpressionId ann mapping x =
  case Map.lookup x (mapping ^. #subexpressionIds . #constants) of
    Just sId -> pure (sId ^. #unOf)
    Nothing -> Left (ErrorMessage ann "constant subexpression id not found")

logicTermSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  LC.Term ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace, SubexpressionId, Scalar)
logicTermSubexpressionTraces ann lc arg mapping tables c =
  \case
    LC.Plus x y -> do
      (m0, s0, x') <- rec x
      (m1, s1, y') <- rec y
      s2 <- getOperationSubexpressionId ann mapping (Plus' s0 s1)
      let v = x' Group.+ y'
          m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #plus . #unOf) defaultAdvice)
      pure (m0 <> m1 <> m2, s2, v)
    LC.Times x y -> do
      (m0, s0, x') <- rec x
      if x' == zero
        then do
          s1 <- getOperationSubexpressionId ann mapping (TimesAndShortCircuit' s0)
          let m1 = Map.singleton s1 (SubexpressionTrace zero (mapping ^. #stepTypeIds . #timesAndShortCircuit . #unOf) defaultAdvice)
          pure (m0 <> m1, s1, zero)
        else do
          (m1, s1, y') <- rec y
          s2 <- getOperationSubexpressionId ann mapping (TimesAnd' s0 s1)
          let v = x' Ring.* y'
              m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #timesAnd . #unOf) defaultAdvice)
          pure (m0 <> m1 <> m2, s2, v)
    LC.Max x y -> do
      (m0, s0, x') <- rec x
      (m1, s1, y') <- rec y
      s2 <- getOperationSubexpressionId ann mapping (Max' s0 s1)
      let v = x' `max` y'
          m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #maxT . #unOf) defaultAdvice)
      pure (m0 <> m1 <> m2, s2, v)
    LC.IndLess x y -> do
      (m0, s0, x') <- rec x
      (m1, s1, y') <- rec y
      s2 <- getOperationSubexpressionId ann mapping (LessThan' s0 s1)
      let v = x' `lessIndicator` y'
          m2 = Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #lessThan . #unOf) defaultAdvice)
      pure (m0 <> m1 <> m2, s2, v)
    LC.Const x -> do
      st <- getConstantStepTypeId ann mapping x
      s <- getConstantSubexpressionId ann mapping x
      pure (Map.singleton s (SubexpressionTrace x st defaultAdvice), s, x)
    LC.Var x -> var x
    LC.Lookup is o -> lkup is o
  where
    rec = logicTermSubexpressionTraces ann lc arg mapping tables c
    var = polyVarSubexpressionTraces ann arg mapping c
    lkup = lookupTermSubexpressionTraces ann lc arg mapping tables c
    defaultAdvice = getDefaultAdvice mapping

polyVarSubexpressionTraces ::
  ann ->
  LC.Argument ->
  Mapping ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace, SubexpressionId, Scalar)
polyVarSubexpressionTraces ann arg mapping c x =
  if x ^. #rowIndex == 0
    then polyVarSameCaseSubexpressionTraces ann arg mapping c x
    else polyVarDifferentCaseSubexpressionTraces ann arg mapping c x

polyVarSameCaseSubexpressionTraces ::
  ann ->
  LC.Argument ->
  Mapping ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace, SubexpressionId, Scalar)
polyVarSameCaseSubexpressionTraces ann arg mapping c x = do
  st <- maybe (Left (ErrorMessage ann "load step type lookup failed"))
          pure (Map.lookup x (mapping ^. #stepTypeIds . #loads))
  sId <- maybe (Left (ErrorMessage ann "variable subexpression id lookup failed"))
           (pure . (^. #unOf)) (Map.lookup x (mapping ^. #subexpressionIds . #variables))
  v <- polyVarValue ann arg c x
  pure (Map.singleton sId (SubexpressionTrace v st defaultAdvice), sId, v)
  where
    defaultAdvice = getDefaultAdvice mapping

polyVarValue ::
  ann ->
  LC.Argument ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) Scalar
polyVarValue ann arg c v = do
  ri <- maybe (Left (ErrorMessage ann "row index exceeds max Int"))
          pure (integerToInt (scalarToInteger (c ^. #unCase)))
  let ref = CellReference (v ^. #colIndex)
              (RowIndex (ri + (v ^. #rowIndex . #getRowIndex)))
  case Map.lookup ref (arg ^. #statement . #unStatement) of
    Just x -> pure x
    Nothing ->
      maybe (Left (ErrorMessage ann "variable not defined"))
        pure (Map.lookup ref (arg ^. #witness . #unWitness))

polyVarDifferentCaseSubexpressionTraces ::
  ann ->
  LC.Argument ->
  Mapping ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace, SubexpressionId, Scalar)
polyVarDifferentCaseSubexpressionTraces ann arg mapping c x = do
  let st = mapping ^. #stepTypeIds . #loadFromDifferentCase . #unOf
  sId <- maybe (Left (ErrorMessage ann "variable subexpression id lookup failed"))
           (pure . (^. #unOf)) (Map.lookup x (mapping ^. #subexpressionIds . #variables))
  v <- polyVarValue ann arg c x
  pure (Map.singleton sId (SubexpressionTrace v st defaultAdvice), sId, v)
  where
    defaultAdvice = getDefaultAdvice mapping

lookupTermSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  [(InputExpression LC.Term, LookupTableColumn)] ->
  LC.LookupTableOutputColumn ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace, SubexpressionId, Scalar)
lookupTermSubexpressionTraces ann lc arg mapping tables c lookupArg outCol = do
  inputs' <-
    Map.fromList
      . zip (snd <$> lookupArg)
      <$> mapM (term . (^. #getInputExpression) . fst) lookupArg
  v <- maybe (Left (ErrorMessage ann "lookup term lookup failed"))
         pure
         (Map.lookup
           (Set.fromList (snd <$> lookupArg), outCol)
           (tables ^. #lookupTermCaches)
             >>= Map.lookup (inputs' <&> (^. _3)))
  st <- maybe (Left (ErrorMessage ann "step type lookup failed"))
          pure
          (Map.lookup
            (LookupTable
              ((snd <$> lookupArg) <>
                [outCol ^. #unLookupTableOutputColumn]))
            (mapping ^. #stepTypeIds . #lookupTables))
  sId <- 
    maybe (Left (ErrorMessage ann "lookup subexpression id lookup failed"))
      (pure . (^. #unBareLookupSubexpressionId))
      (Map.lookup
        (BareLookupArgument lookupArg)
        (mapping ^. #subexpressionIds . #bareLookups))
  let ms = inputs' <&> (^. _1)
      m' = Map.singleton sId (SubexpressionTrace v st defaultAdvice)
  pure (mconcat (Map.elems ms) <> m', sId, v)
  where
    term = logicTermSubexpressionTraces ann lc arg mapping tables c
    defaultAdvice = getDefaultAdvice mapping

lookupArgumentSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  LookupArgument LC.Term ->
  Either (ErrorMessage ann) (Map SubexpressionId SubexpressionTrace)
lookupArgumentSubexpressionTraces = todo

logicCircuitStatementToTraceStatement ::
  ann ->
  LC.Statement ->
  Either (ErrorMessage ann) Statement
logicCircuitStatementToTraceStatement ann stmt =
  Statement <$> cellMapToCaseAndColMap ann (stmt ^. #unStatement)

logicCircuitWitnessToTraceWitness ::
  ann ->
  LC.Witness ->
  Either (ErrorMessage ann) Witness
logicCircuitWitnessToTraceWitness ann witness =
  Witness <$> cellMapToCaseAndColMap ann (witness ^. #unWitness)

cellMapToCaseAndColMap ::
  ann ->
  Map CellReference Scalar ->
  Either (ErrorMessage ann) (Map (Case, ColumnIndex) Scalar)
cellMapToCaseAndColMap ann cellMap =
  Map.fromList <$> sequence
    [ (,)
        <$> ((,col) . Case <$>
              maybe (Left (ErrorMessage ann "row index out of range of scalar field"))
                pure (integerToScalar (intToInteger (row ^. #getRowIndex))))
        <*> pure x
      | (CellReference col row, x) <- Map.toList cellMap
    ]

todo :: a
todo = todo

logicCircuitToTraceType ::
  BitsPerByte ->
  LogicCircuit ->
  TraceType
logicCircuitToTraceType bitsPerByte c =
  TraceType
    colTypes'
    (c ^. #equalityConstrainableColumns)
    (c ^. #equalityConstraints)
    stepTypes
    subexprs
    (getSubexpressionLinks mapping)
    (getResultExpressionIds mapping)
    (mapping ^. #caseNumber)
    (mapping ^. #stepType)
    (mapping ^. #stepIndicator)
    (mapping ^. #inputs)
    (mapping ^. #output)
    (NumberOfCases (rowCount ^. #getRowCount))
    (rowCount * RowCount (maxStepsPerCase subexprs))
  where
    rowCount = c ^. #rowCount

    mapping = getMapping bitsPerByte c

    colTypes' = getColumnTypes c mapping

    stepTypes = getStepTypes bitsPerByte c mapping

    subexprs = getSubexpressionIdSet (mapping ^. #subexpressionIds)

-- TODO: let the columns be reused where possible
data Mapping = Mapping
  { caseNumber :: CaseNumberColumnIndex,
    stepType :: StepTypeColumnIndex,
    stepIndicator :: StepIndicatorColumnIndex,
    inputs :: [InputColumnIndex],
    output :: OutputColumnIndex,
    byteDecomposition :: ByteDecompositionMapping,
    truthTable :: TruthTableColumnIndices,
    stepTypeIds :: StepTypeIdMapping,
    subexpressionIds :: SubexpressionIdMapping
  }
  deriving (Generic)

data ByteDecompositionMapping = ByteDecompositionMapping
  { bits :: BitsPerByte,
    sign :: SignColumnIndex,
    bytes :: [(ByteColumnIndex, TruthValueColumnIndex)] -- most significant first
  }
  deriving (Generic)

newtype TruthValueColumnIndex = TruthValueColumnIndex
  {unTruthValueColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype SignColumnIndex = SignColumnIndex {unSignColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype ByteColumnIndex = ByteColumnIndex {unByteColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype ByteRangeColumnIndex = ByteRangeColumnIndex
  {unByteRangeColumnIndex :: ColumnIndex}
  deriving (Generic)

newtype ZeroIndicatorColumnIndex = ZeroIndicatorColumnIndex
  {unZeroIndicatorColumnIndex :: ColumnIndex}
  deriving (Generic)

data TruthTableColumnIndices = TruthTableColumnIndices
  { byteRangeColumnIndex :: ByteRangeColumnIndex,
    zeroIndicatorColumnIndex :: ZeroIndicatorColumnIndex
  }
  deriving (Generic)

data Operator
  = Plus
  | TimesAnd -- (*) and (&) are the same operation, actually
  | TimesAndShortCircuit -- first argument is zero / false
  | Or
  | OrShortCircuit -- first argument is true
  | Not
  | Iff
  | Equals
  | LessThan
  | Max
  | VoidT
  | AssertT
  | AssertLookupT
  | LoadFromDifferentCase

type StepTypeIdOf :: Operator -> Type
newtype StepTypeIdOf a = StepTypeIdOf {unOf :: StepTypeId}
  deriving (Generic)

newtype LookupTable = LookupTable {unLookupTable :: [LookupTableColumn]}
  deriving (Eq, Ord, Generic)

newtype BareLookupArgument = BareLookupArgument
  { getBareLookupArgument ::
      [(InputExpression LC.Term, LookupTableColumn)]
  }
  deriving (Eq, Ord, Generic)

data StepTypeIdMapping = StepTypeIdMapping
  { loads :: Map PolynomialVariable StepTypeId,
    loadFromDifferentCase :: StepTypeIdOf LoadFromDifferentCase,
    lookupTables :: Map LookupTable StepTypeId,
    assertLookup :: StepTypeIdOf AssertLookupT,
    constants :: Map Scalar StepTypeId,
    plus :: StepTypeIdOf Plus,
    timesAnd :: StepTypeIdOf TimesAnd,
    timesAndShortCircuit :: StepTypeIdOf TimesAndShortCircuit,
    or :: StepTypeIdOf Or,
    orShortCircuit :: StepTypeIdOf OrShortCircuit,
    not :: StepTypeIdOf Not,
    iff :: StepTypeIdOf Iff,
    equals :: StepTypeIdOf Equals,
    lessThan :: StepTypeIdOf LessThan,
    maxT :: StepTypeIdOf Max,
    voidT :: StepTypeIdOf VoidT,
    assertT :: StepTypeIdOf AssertT
  }
  deriving (Generic)

type SubexpressionIdOf :: Type -> Type
newtype SubexpressionIdOf a = SubexpressionIdOf {unOf :: SubexpressionId}
  deriving (Generic)

type Void :: Type
data Void

data Operation
  = Or' SubexpressionId SubexpressionId
  | OrShortCircuit' SubexpressionId
  | Not' SubexpressionId
  | Iff' SubexpressionId SubexpressionId
  | Plus' SubexpressionId SubexpressionId
  | TimesAnd' SubexpressionId SubexpressionId
  | TimesAndShortCircuit' SubexpressionId
  | Equals' SubexpressionId SubexpressionId
  | LessThan' SubexpressionId SubexpressionId
  | Max' SubexpressionId SubexpressionId
  deriving (Eq, Ord)

data Assertion = Assertion
  { input :: InputSubexpressionId,
    output :: OutputSubexpressionId
  }
  deriving (Eq, Ord, Generic)

newtype BareLookupSubexpressionId = BareLookupSubexpressionId {unBareLookupSubexpressionId :: SubexpressionId}
  deriving (Eq, Ord, Generic)

data GateSubexpressionIds = GateSubexpressionIds
  { input :: InputSubexpressionId,
    output :: OutputSubexpressionId
  }
  deriving (Eq, Ord, Generic)

data LookupAssertion = LookupAssertion
  { bareLookup :: BareLookupSubexpressionId,
    gate :: GateSubexpressionIds,
    output :: OutputSubexpressionId
  }
  deriving (Eq, Ord, Generic)

data SubexpressionIdMapping = SubexpressionIdMapping
  { void :: Maybe (SubexpressionIdOf Void),
    assertions :: Set Assertion,
    variables :: Map PolynomialVariable (SubexpressionIdOf PolynomialVariable),
    bareLookups :: Map BareLookupArgument BareLookupSubexpressionId,
    lookupAssertions :: Set LookupAssertion,
    constants :: Map Scalar (SubexpressionIdOf Scalar),
    operations :: Map Operation (SubexpressionIdOf Operation)
  }
  deriving (Generic)

instance Semigroup SubexpressionIdMapping where
  (SubexpressionIdMapping b c d e f g h) <> (SubexpressionIdMapping j k l m n o p) =
    SubexpressionIdMapping
      (b <|> j)
      (c <> k)
      (d <> l)
      (e <> m)
      (f <> n)
      (g <> o)
      (h <> p)

getStepArity :: LogicCircuit -> Arity
getStepArity c =
  max (max 2 (foldl' max 0 (getConstraintArity . snd <$> (c ^. #gateConstraints . #constraints)))) $
    getLookupArgumentsArity (c ^. #lookupArguments)

getConstraintArity :: LogicConstraint -> Arity
getConstraintArity =
  \case
    LC.Atom (LC.Equals x y) -> term x `max` term y
    LC.Atom (LC.LessThan x y) -> term x `max` term y
    LC.And p q -> rec p `max` rec q
    LC.Or p q -> rec p `max` rec q
    LC.Iff p q -> rec p `max` rec q
    LC.Not p -> rec p
    LC.Top -> 0
    LC.Bottom -> 0
  where
    term = getTermArity
    rec = getConstraintArity

getTermArity :: LC.Term -> Arity
getTermArity =
  \case
    LC.Const _ -> 0
    LC.Var _ -> 0
    LC.Lookup is _ ->
      (1 + Arity (length is))
        `max` foldl' max 0 (getInputExpressionArity . fst <$> is)
    LC.Plus x y -> rec x `max` rec y
    LC.Times x y -> rec x `max` rec y
    LC.Max x y -> rec x `max` rec y
    LC.IndLess x y -> rec x `max` rec y
  where
    rec = getTermArity

getInputExpressionArity :: InputExpression LC.Term -> Arity
getInputExpressionArity = getTermArity . (^. #getInputExpression)

getLookupArgumentsArity :: LookupArguments a -> Arity
getLookupArgumentsArity =
  foldl' max 0 . fmap (Arity . length . (^. #tableMap)) . Set.toList
    . (^. #getLookupArguments)

getByteDecompositionLength :: BitsPerByte -> LogicCircuit -> Int
getByteDecompositionLength bitsPerByte c =
  foldl' max 1 . fmap (countBytes bitsPerByte)
    . Map.elems
    $ c ^. #gateConstraints . #bounds

data S = S
  { nextColumnIndex :: ColumnIndex,
    nextStepTypeId :: StepTypeId,
    nextSubexpressionId :: SubexpressionId
  }
  deriving (Generic)

getMapping :: BitsPerByte -> LogicCircuit -> Mapping
getMapping bitsPerByte c =
  evalState go initialState
  where
    initialState :: S
    initialState =
      S
        (ColumnIndex (length (Map.keys (c ^. #columnTypes . #getColumnTypes))))
        (StepTypeId zero)
        (SubexpressionId zero)

    nextCol :: State S ColumnIndex
    nextCol = do
      S i j k <- get
      put (S (i + 1) j k)
      pure i

    nextSid :: State S StepTypeId
    nextSid = do
      S i j k <- get
      put (S i (j + StepTypeId one) k)
      pure j

    nextSid' :: State S (StepTypeIdOf a)
    nextSid' = StepTypeIdOf <$> nextSid

    nextEid :: State S SubexpressionId
    nextEid = do
      S i j k <- get
      put (S i j (k + SubexpressionId one))
      pure k

    nextEid' :: State S (SubexpressionIdOf a)
    nextEid' = SubexpressionIdOf <$> nextEid

    go :: State S Mapping
    go = do
      cnc <- CaseNumberColumnIndex <$> nextCol
      stc <- StepTypeColumnIndex <$> nextCol
      sic <- StepIndicatorColumnIndex <$> nextCol
      ins <-
        replicateM
          (getStepArity c ^. #unArity)
          (InputColumnIndex <$> nextCol)
      out <- OutputColumnIndex <$> nextCol
      polyVarsZeroOffsetMapping <-
        Map.fromList . zip polyVarsZeroOffset
          <$> replicateM (length polyVarsZeroOffset) nextSid
      let scalars' = scalars polyVarsZeroOffsetMapping
      Mapping cnc stc sic ins out
        <$> ( ByteDecompositionMapping bitsPerByte
                <$> (SignColumnIndex <$> nextCol)
                <*> replicateM
                  (getByteDecompositionLength bitsPerByte c)
                  ( (,) <$> (ByteColumnIndex <$> nextCol)
                      <*> (TruthValueColumnIndex <$> nextCol)
                  )
            )
        <*> ( TruthTableColumnIndices
                <$> (ByteRangeColumnIndex <$> nextCol)
                <*> (ZeroIndicatorColumnIndex <$> nextCol)
            )
        <*> ( StepTypeIdMapping polyVarsZeroOffsetMapping
                <$> (nextSid' :: State S (StepTypeIdOf LoadFromDifferentCase))
                <*> ( Map.fromList . zip lookupTables'
                        <$> replicateM (length lookupTables') nextSid
                    )
                <*> (nextSid' :: State S (StepTypeIdOf AssertLookupT))
                <*> ( Map.fromList . zip scalars'
                        <$> replicateM (length scalars') nextSid
                    )
                <*> (nextSid' :: State S (StepTypeIdOf Plus))
                <*> (nextSid' :: State S (StepTypeIdOf TimesAnd))
                <*> (nextSid' :: State S (StepTypeIdOf TimesAndShortCircuit))
                <*> (nextSid' :: State S (StepTypeIdOf Or))
                <*> (nextSid' :: State S (StepTypeIdOf OrShortCircuit))
                <*> (nextSid' :: State S (StepTypeIdOf Not))
                <*> (nextSid' :: State S (StepTypeIdOf Iff))
                <*> (nextSid' :: State S (StepTypeIdOf Equals))
                <*> (nextSid' :: State S (StepTypeIdOf LessThan))
                <*> (nextSid' :: State S (StepTypeIdOf Max))
                <*> (nextSid' :: State S (StepTypeIdOf VoidT))
                <*> (nextSid' :: State S (StepTypeIdOf AssertT))
            )
        <*> ( do
                m0 <-
                  SubexpressionIdMapping
                    <$> (Just <$> (nextEid' :: State S (SubexpressionIdOf Void)))
                    <*> pure mempty
                    <*> ( Map.fromList . zip polyVars
                            <$> replicateM (length polyVars) nextEid'
                        )
                    <*> ( Map.fromList . zip bareLookupArguments
                            <$> replicateM
                              (length bareLookupArguments)
                              (BareLookupSubexpressionId <$> nextEid)
                        )
                    <*> pure mempty
                    <*> ( Map.fromList . zip scalars'
                            <$> replicateM (length scalars') nextEid'
                        )
                    <*> pure mempty
                traverseLookupArguments out (c ^. #lookupArguments)
                  =<< traverseLogicConstraints out m0 (c ^. #gateConstraints)
            )

    traverseLookupArguments :: OutputColumnIndex -> LookupArguments LC.Term -> SubexpressionIdMapping -> State S SubexpressionIdMapping
    traverseLookupArguments out args m' =
      foldM (traverseLookupArgument out) m' (args ^. #getLookupArguments)

    traverseLookupArgument :: OutputColumnIndex -> SubexpressionIdMapping -> LookupArgument LC.Term -> State S SubexpressionIdMapping
    traverseLookupArgument out m' arg = do
      (gateId, m'') <- traverseLookupGate out m' (arg ^. #gate)
      (bareLookupId, m''') <- traverseBareLookupArgument out m'' (BareLookupArgument (arg ^. #tableMap))
      addLookupAssertion m''' . LookupAssertion bareLookupId gateId
        . OutputSubexpressionId
        <$> nextEid

    traverseLookupGate :: OutputColumnIndex -> SubexpressionIdMapping -> LC.Term -> State S (GateSubexpressionIds, SubexpressionIdMapping)
    traverseLookupGate out m' x = do
      (inId, m'') <- traverseTerm out m' x
      (outId, m''') <- addOp m'' (Equals' (zeroEid m'') inId) <$> nextEid'
      pure (GateSubexpressionIds (InputSubexpressionId inId) (OutputSubexpressionId outId), m''')

    traverseBareLookupArgument :: OutputColumnIndex -> SubexpressionIdMapping -> BareLookupArgument -> State S (BareLookupSubexpressionId, SubexpressionIdMapping)
    traverseBareLookupArgument out m' arg = do
      m'' <-
        foldM
          (\m'' e -> snd <$> traverseTerm out m'' (fst e ^. #getInputExpression))
          m'
          (arg ^. #getBareLookupArgument)
      case Map.lookup arg (m' ^. #bareLookups) of
        Just bareLookupId -> pure (bareLookupId, m'')
        Nothing -> do
          eid <- BareLookupSubexpressionId <$> nextEid
          let m''' = m'' <> SubexpressionIdMapping mzero mempty mempty (Map.singleton arg eid) mempty mempty mempty
          pure (eid, m''')

    traverseLogicConstraints :: OutputColumnIndex -> SubexpressionIdMapping -> LogicConstraints -> State S SubexpressionIdMapping
    traverseLogicConstraints out m' lcs =
      foldM (traverseAssertion out) m' (snd <$> (lcs ^. #constraints))

    traverseAssertion :: OutputColumnIndex -> SubexpressionIdMapping -> LogicConstraint -> State S SubexpressionIdMapping
    traverseAssertion out m' lc = do
      (inEid, m'') <- traverseConstraint out m' lc
      outEid <- OutputSubexpressionId <$> nextEid
      pure (addAssertion m'' (Assertion (InputSubexpressionId inEid) outEid))

    traverseConstraint :: OutputColumnIndex -> SubexpressionIdMapping -> LogicConstraint -> State S (SubexpressionId, SubexpressionIdMapping)
    traverseConstraint out m' =
      \case
        LC.Atom x -> traverseAtom out m' x
        LC.Not x -> do
          (xId, m'') <- traverseConstraint out m' x
          addOp m'' (Not' xId) <$> nextEid'
        LC.And x y -> do
          (xId, m'') <- traverseConstraint out m' x
          (yId, m''') <- traverseConstraint out m'' y
          (zId, m'''') <- addOp m''' (TimesAnd' xId yId) <$> nextEid'
          pure $ addOp m'''' (TimesAndShortCircuit' xId) (SubexpressionIdOf zId)
        LC.Or x y -> do
          (xId, m'') <- traverseConstraint out m' x
          (yId, m''') <- traverseConstraint out m'' y
          (zId, m'''') <- addOp m''' (Or' xId yId) <$> nextEid'
          pure $ addOp m'''' (OrShortCircuit' xId) (SubexpressionIdOf zId)
        LC.Iff x y -> do
          (xId, m'') <- traverseConstraint out m' x
          (yId, m''') <- traverseConstraint out m'' y
          addOp m''' (Iff' xId yId) <$> nextEid'
        LC.Top -> pure (oneEid m', m')
        LC.Bottom -> pure (zeroEid m', m')

    zeroEid, oneEid :: SubexpressionIdMapping -> SubexpressionId
    zeroEid m' =
      case Map.lookup zero (m' ^. #constants) of
        Just eid -> eid ^. #unOf
        Nothing -> die "zeroEid: no zero subexpression id (this is a compiler bug)"
    oneEid m' =
      case Map.lookup one (m' ^. #constants) of
        Just eid -> eid ^. #unOf
        Nothing -> die "oneEid: no one subexpression id (this is a compiler bug)"

    addOp ::
      SubexpressionIdMapping ->
      Operation ->
      SubexpressionIdOf Operation ->
      (SubexpressionId, SubexpressionIdMapping)
    addOp m' op opId =
      case Map.lookup op (m' ^. #operations) of
        Just opId' -> (opId' ^. #unOf, m')
        Nothing -> (opId ^. #unOf, m' <> SubexpressionIdMapping mzero mempty mempty mempty mempty mempty (Map.singleton op opId))

    addAssertion ::
      SubexpressionIdMapping ->
      Assertion ->
      SubexpressionIdMapping
    addAssertion m' a =
      m' <> SubexpressionIdMapping mzero (Set.singleton a) mempty mempty mempty mempty mempty

    addLookupAssertion ::
      SubexpressionIdMapping ->
      LookupAssertion ->
      SubexpressionIdMapping
    addLookupAssertion m' a =
      m' <> SubexpressionIdMapping mzero mempty mempty mempty (Set.singleton a) mempty mempty

    traverseAtom ::
      OutputColumnIndex ->
      SubexpressionIdMapping ->
      AtomicLogicConstraint ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traverseAtom out m' =
      \case
        LC.Equals x y -> do
          (xId, m'') <- traverseTerm out m' x
          (yId, m''') <- traverseTerm out m'' y
          addOp m''' (Equals' xId yId) <$> nextEid'
        LC.LessThan x y -> do
          (xId, m'') <- traverseTerm out m' x
          (yId, m''') <- traverseTerm out m'' y
          addOp m''' (LessThan' xId yId) <$> nextEid'

    traverseTerm ::
      OutputColumnIndex ->
      SubexpressionIdMapping ->
      LC.Term ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traverseTerm out m' =
      \case
        LC.Var x -> pure (varEid m' x, m')
        LC.Lookup is (LC.LookupTableOutputColumn o) -> do
          (eid, m'') <-
            traverseBareLookupArgument out m' . BareLookupArgument $
              is
                <> [ ( InputExpression (LC.Var (PolynomialVariable (out ^. #unOutputColumnIndex) 0)),
                       o
                     )
                   ]
          pure (eid ^. #unBareLookupSubexpressionId, m'')
        LC.Const x -> pure (constantEid m' x, m')
        LC.Plus x y -> do
          (xEid, m'') <- traverseTerm out m' x
          (yEid, m''') <- traverseTerm out m'' y
          addOp m''' (Plus' xEid yEid) <$> nextEid'
        LC.Times x y -> do
          (xEid, m'') <- traverseTerm out m' x
          (yEid, m''') <- traverseTerm out m'' y
          addOp m''' (TimesAnd' xEid yEid) <$> nextEid'
        LC.Max x y -> do
          (xEid, m'') <- traverseTerm out m' x
          (yEid, m''') <- traverseTerm out m'' y
          addOp m''' (Max' xEid yEid) <$> nextEid'
        LC.IndLess x y -> do
          (xEid, m'') <- traverseTerm out m' x
          (yEid, m''') <- traverseTerm out m'' y
          addOp m''' (LessThan' xEid yEid) <$> nextEid'

    varEid :: SubexpressionIdMapping -> PolynomialVariable -> SubexpressionId
    varEid m' x =
      case Map.lookup x (m' ^. #variables) of
        Just eid -> eid ^. #unOf
        Nothing -> die "varEid: variable lookup failed (this is a compiler bug)"

    constantEid ::
      SubexpressionIdMapping ->
      Scalar ->
      SubexpressionId
    constantEid m' a =
      case Map.lookup a (m' ^. #constants) of
        Just eid -> eid ^. #unOf
        Nothing -> die "coefficientEid: coefficient lookup failed (this is a compiler bug)"

    polyVars :: [PolynomialVariable]
    polyVars =
      let vs = getPolynomialVariables c
       in Set.toList (vs <> Set.map (\x -> PolynomialVariable (x ^. #colIndex) 0) vs)

    polyVarsZeroOffset :: [PolynomialVariable]
    polyVarsZeroOffset = filter ((== 0) . (^. #rowIndex)) polyVars

    lookupTables' :: [LookupTable]
    lookupTables' =
      LookupTable . snd
        <$> Set.toList (getLookupTables @LogicCircuit @LC.Term c)

    bareLookupArguments :: [BareLookupArgument]
    bareLookupArguments =
      Set.toList . Set.fromList $ -- this appears redundant but is actually there to eliminate redundancy
        BareLookupArgument . (^. #tableMap)
          <$> Set.toList (getLookupArguments c ^. #getLookupArguments)

    rowIndexToScalar :: RowIndex a -> Scalar
    rowIndexToScalar =
      fromMaybe (die "getMapping: could not convert row index to scalar (this is a compiler bug)")
        . integerToScalar
        . intToInteger
        . (^. #getRowIndex)

    scalars :: Map PolynomialVariable StepTypeId -> [Scalar]
    scalars polyVarsZeroOffsetMapping =
      Set.toList $
        mconcat
          [ getScalars c,
            Set.fromList ((^. #unStepTypeId) <$> Map.elems polyVarsZeroOffsetMapping),
            Set.fromList (rowIndexToScalar . (^. #rowIndex) <$> polyVars)
          ]

getColumnTypes :: LogicCircuit -> Mapping -> ColumnTypes
getColumnTypes c mapping =
  (c ^. #columnTypes)
    <> ( ColumnTypes . Map.fromList $
           (,Advice) <$> getMappingIndices mapping
       )

getMappingIndices :: Mapping -> [ColumnIndex]
getMappingIndices m =
  [ m ^. #caseNumber . #unCaseNumberColumnIndex,
    m ^. #stepType . #unStepTypeColumnIndex,
    m ^. #stepIndicator . #unStepIndicatorColumnIndex
  ]
    <> ((m ^. #inputs) <&> (^. #unInputColumnIndex))
    <> [ m ^. #output . #unOutputColumnIndex,
         m ^. #byteDecomposition . #sign . #unSignColumnIndex
       ]
    <> concatMap
      ( \(i, j) ->
          [ i ^. #unByteColumnIndex,
            j ^. #unTruthValueColumnIndex
          ]
      )
      (m ^. #byteDecomposition . #bytes)
    <> [ m ^. #truthTable . #byteRangeColumnIndex . #unByteRangeColumnIndex,
         m ^. #truthTable . #zeroIndicatorColumnIndex . #unZeroIndicatorColumnIndex
       ]

getStepTypes ::
  BitsPerByte ->
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType
getStepTypes bitsPerByte c m =
  mconcat
    [ loadStepTypes m,
      bareLookupStepTypes m,
      constantStepTypes m,
      operatorStepTypes bitsPerByte c m,
      assertStepType m,
      assertLookupStepType m
    ]

loadStepTypes ::
  Mapping ->
  Map StepTypeId StepType
loadStepTypes m =
  Map.fromList $
    [ ( m ^. #stepTypeIds . #loadFromDifferentCase . #unOf,
        loadFromDifferentCaseStepType m
      )
    ]
      <> catMaybes
        [ (sId,) <$> loadStepType m x
          | (x, sId) <- Map.toList (m ^. #stepTypeIds . #loads)
        ]

loadStepType ::
  Mapping ->
  PolynomialVariable ->
  Maybe StepType
loadStepType m x =
  if (x ^. #rowIndex) == 0
    then Just $ loadFromSameCaseStepType m (x ^. #colIndex)
    else Nothing

loadFromSameCaseStepType ::
  Mapping ->
  ColumnIndex ->
  StepType
loadFromSameCaseStepType m i =
  StepType
    ( PolynomialConstraints
        [ P.minus
            (P.var' i)
            (P.var' (m ^. #output . #unOutputColumnIndex))
        ]
        1
    )
    mempty
    mempty

loadFromDifferentCaseStepType ::
  Mapping ->
  StepType
loadFromDifferentCaseStepType m =
  StepType
    mempty
    ( LookupArguments . Set.singleton $
        LookupArgument
          "loadFromDifferentCase"
          P.zero
          [(o, os), (c, cs), (t, ts)]
    )
    mempty
  where
    (i0, i1) = firstTwoInputs m

    o, c, t :: InputExpression Polynomial
    o = InputExpression (P.var' (m ^. #output . #unOutputColumnIndex))
    c =
      InputExpression $
        P.var' (m ^. #caseNumber . #unCaseNumberColumnIndex)
          `P.plus` P.var' (i1 ^. #unInputColumnIndex)
    t = InputExpression (P.var' (i0 ^. #unInputColumnIndex))

    os, cs, ts :: LookupTableColumn
    os = LookupTableColumn (m ^. #output . #unOutputColumnIndex)
    cs = LookupTableColumn (m ^. #caseNumber . #unCaseNumberColumnIndex)
    ts = LookupTableColumn (m ^. #stepType . #unStepTypeColumnIndex)

bareLookupStepTypes ::
  Mapping ->
  Map StepTypeId StepType
bareLookupStepTypes m =
  Map.fromList
    [ (sId, lookupStepType m P.zero t)
      | (t, sId) <- Map.toList (m ^. #stepTypeIds . #lookupTables)
    ]

lookupStepType ::
  Mapping ->
  Polynomial ->
  LookupTable ->
  StepType
lookupStepType m p (LookupTable t) =
  StepType
    mempty
    ( LookupArguments . Set.singleton $
        LookupArgument (Label ("lookup-" <> show t)) p (zip inputExprs t)
    )
    mempty
  where
    inputExprs :: [InputExpression Polynomial]
    inputExprs =
      InputExpression . P.var' . (^. #unInputColumnIndex)
        <$> (m ^. #inputs)

constantStepTypes ::
  Mapping ->
  Map StepTypeId StepType
constantStepTypes m =
  Map.fromList
    [ (sId, constantStepType m x)
      | (x, sId) <- Map.toList (m ^. #stepTypeIds . #constants)
    ]

constantStepType :: Mapping -> Scalar -> StepType
constantStepType m x =
  StepType
    ( PolynomialConstraints
        [ P.minus
            (P.constant x)
            (P.var' (m ^. #output . #unOutputColumnIndex))
        ]
        1
    )
    mempty
    mempty

operatorStepTypes ::
  BitsPerByte ->
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType
operatorStepTypes bitsPerByte c m =
  mconcat
    [ plusStepType m,
      timesStepType m,
      timesShortCircuitStepType m,
      orStepType m,
      orShortCircuitStepType m,
      notStepType m,
      iffStepType m,
      equalsStepType bitsPerByte c m,
      lessThanStepType bitsPerByte c m,
      maxStepType bitsPerByte c m,
      voidStepType m
    ]

firstTwoInputs ::
  Mapping ->
  (InputColumnIndex, InputColumnIndex)
firstTwoInputs m =
  case m ^. #inputs of
    (i0 : i1 : _) -> (i0, i1)
    _ -> die "firstTwoInputs: there are not two inputs (this is a compiler bug)"

plusStepType,
  timesStepType,
  timesShortCircuitStepType,
  orStepType,
  orShortCircuitStepType,
  notStepType,
  iffStepType,
  voidStepType ::
    Mapping ->
    Map StepTypeId StepType
plusStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #plus . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.minus
                (P.var' (m ^. #output . #unOutputColumnIndex))
                ( P.plus
                    (P.var' (i0 ^. #unInputColumnIndex))
                    (P.var' (i1 ^. #unInputColumnIndex))
                )
            ]
            1
        )
        mempty
        mempty
    )
  where
    (i0, i1) = firstTwoInputs m
timesStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #timesAnd . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.minus
                (P.var' (m ^. #output . #unOutputColumnIndex))
                ( P.times
                    (P.var' (i0 ^. #unInputColumnIndex))
                    (P.var' (i1 ^. #unInputColumnIndex))
                )
            ]
            2
        )
        mempty
        mempty
    )
  where
    (i0, i1) = firstTwoInputs m
timesShortCircuitStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #timesAndShortCircuit . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.var' (m ^. #output . #unOutputColumnIndex),
              P.var' (i0 ^. #unInputColumnIndex)
            ]
            2
        )
        mempty
        mempty
    )
  where
    (i0, _) = firstTwoInputs m
orStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #or . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.minus
                (P.var' (m ^. #output . #unOutputColumnIndex))
                (P.plus v0 (P.minus v1 (P.times v0 v1)))
            ]
            2
        )
        mempty
        mempty
    )
  where
    (i0, i1) = firstTwoInputs m
    v0 = P.var' (i0 ^. #unInputColumnIndex)
    v1 = P.var' (i1 ^. #unInputColumnIndex)
orShortCircuitStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #orShortCircuit . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.minus P.one (P.var' (m ^. #output . #unOutputColumnIndex)),
              P.minus P.one (P.var' (i0 ^. #unInputColumnIndex))
            ]
            2
        )
        mempty
        mempty
    )
  where
    (i0, _) = firstTwoInputs m
notStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #not . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.minus
                (P.var' (m ^. #output . #unOutputColumnIndex))
                (P.minus P.one (P.var' (i0 ^. #unInputColumnIndex)))
            ]
            1
        )
        mempty
        mempty
    )
  where
    (i0, _) = firstTwoInputs m
iffStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #iff . #unOf)
    ( StepType
        ( PolynomialConstraints
            [ P.minus
                (P.var' (m ^. #output . #unOutputColumnIndex))
                ( P.minus
                    P.one
                    ( P.minus
                        (P.var' (i0 ^. #unInputColumnIndex))
                        (P.var' (i1 ^. #unInputColumnIndex))
                    )
                )
            ]
            1
        )
        mempty
        mempty
    )
  where
    (i0, i1) = firstTwoInputs m
voidStepType m =
  Map.singleton (m ^. #stepTypeIds . #voidT . #unOf) mempty

equalsStepType,
  lessThanStepType,
  maxStepType ::
    BitsPerByte ->
    LogicCircuit ->
    Mapping ->
    Map StepTypeId StepType
equalsStepType bitsPerByte c m =
  Map.singleton
    (m ^. #stepTypeIds . #equals . #unOf)
    ( mconcat
        [ StepType
            ( PolynomialConstraints
                [ result `P.times` (result `P.minus` P.one),
                  result `P.times` foldl' P.plus P.zero ((P.one `P.minus`) <$> truthVars)
                ]
                1
            )
            mempty
            mempty,
          byteDecompositionCheck bitsPerByte c m
        ]
    )
  where
    truthVars :: [Polynomial]
    truthVars =
      P.var' . (^. #unTruthValueColumnIndex) . snd
        <$> (m ^. #byteDecomposition . #bytes)

    result :: Polynomial
    result = P.var' $ m ^. #output . #unOutputColumnIndex
lessThanStepType bitsPerByte c m =
  Map.singleton
    (m ^. #stepTypeIds . #lessThan . #unOf)
    ( mconcat
        [ StepType
            ( PolynomialConstraints
                [ result `P.times` (result `P.minus` P.one),
                  (P.one `P.minus` result)
                    `P.times` ( (P.one `P.minus` sign')
                                  `P.times` foldl' P.plus P.zero truthVars
                              ),
                  result
                    `P.times` ( P.one
                                  `P.minus` foldl'
                                    P.times
                                    P.one
                                    [P.one `P.minus` v | v <- truthVars]
                              )
                ]
                (PolynomialDegreeBound (1 + length truthVars))
            )
            mempty
            mempty,
          byteDecompositionCheck bitsPerByte c m
        ]
    )
  where
    truthVars :: [Polynomial]
    truthVars =
      P.var' . (^. #unTruthValueColumnIndex) . snd
        <$> (m ^. #byteDecomposition . #bytes)

    sign' :: Polynomial
    sign' = P.var' (m ^. #byteDecomposition . #sign . #unSignColumnIndex)

    result :: Polynomial
    result = P.var' $ m ^. #output . #unOutputColumnIndex
maxStepType bitsPerByte c m =
  Map.singleton
    (m ^. #stepTypeIds . #maxT . #unOf)
    ( mconcat
        [ StepType
            ( PolynomialConstraints
                [ P.var' out
                    `P.minus` ( (P.var' i1 `P.times` lessInd)
                                  `P.plus` (P.var' i0 `P.times` (P.one `P.minus` lessInd))
                              )
                ]
                (PolynomialDegreeBound 3)
            )
            mempty
            mempty,
          byteDecompositionCheck bitsPerByte c m
        ]
    )
  where
    out, i0, i1 :: ColumnIndex
    lessInd :: Polynomial
    (InputColumnIndex i0, InputColumnIndex i1) = firstTwoInputs m
    out = m ^. #output . #unOutputColumnIndex
    lessInd = (P.one `P.minus` sign') `P.times` truthValueSum
    sign', truthValueSum :: Polynomial
    sign' = P.var' $ m ^. #byteDecomposition . #sign . #unSignColumnIndex
    truthValueSum =
      case snd <$> m ^. #byteDecomposition . #bytes of
        (t : ts) ->
          foldl'
            P.plus
            (P.var' (t ^. #unTruthValueColumnIndex))
            [P.var' $ t' ^. #unTruthValueColumnIndex | t' <- ts]
        [] -> die "maxStepType: no truth values (this is a compiler bug)"

byteDecompositionCheck ::
  BitsPerByte ->
  LogicCircuit ->
  Mapping ->
  StepType
byteDecompositionCheck (BitsPerByte bitsPerByte) c m =
  StepType
    ( PolynomialConstraints
        [ (v0 `P.minus` v1)
            `P.minus` ( ((P.constant two `P.times` s) `P.minus` P.one)
                          `P.times` foldl'
                            P.plus
                            P.zero
                            (zipWith P.times byteCoefs byteVars)
                      ),
          s `P.times` (s `P.minus` P.one)
        ]
        (PolynomialDegreeBound 2)
    )
    (byteRangeAndTruthChecks m)
    (truthTables m)
  where
    (i0, i1) = firstTwoInputs m
    v0 = P.var' (i0 ^. #unInputColumnIndex)
    v1 = P.var' (i1 ^. #unInputColumnIndex)
    s = P.var' (m ^. #byteDecomposition . #sign . #unSignColumnIndex)

    byteCoefs, byteVars :: [Polynomial]
    byteCoefs =
      P.constant . fromMaybe (die "truthTables: byte coefficient is not in range of scalar (this is a compiler bug)") . integerToScalar
        <$> [2 ^ (bitsPerByte * i) | i <- [0 .. getByteDecompositionLength (m ^. #byteDecomposition . #bits) c]]
    byteVars =
      P.var' . (^. #unByteColumnIndex) . fst
        <$> (m ^. #byteDecomposition . #bytes)

byteRangeAndTruthChecks ::
  Mapping ->
  LookupArguments Polynomial
byteRangeAndTruthChecks m =
  LookupArguments $
    Set.fromList
      [ LookupArgument
          "byteRangeAndTruthCheck"
          P.zero
          [ ( InputExpression (P.var' (byteCol ^. #unByteColumnIndex)),
              LookupTableColumn (m ^. #truthTable . #byteRangeColumnIndex . #unByteRangeColumnIndex)
            ),
            ( InputExpression (P.var' (truthCol ^. #unTruthValueColumnIndex)),
              LookupTableColumn (m ^. #truthTable . #zeroIndicatorColumnIndex . #unZeroIndicatorColumnIndex)
            )
          ]
        | (byteCol, truthCol) <- m ^. #byteDecomposition . #bytes
      ]

truthTables ::
  Mapping ->
  FixedValues
truthTables m =
  FixedValues . Map.fromList $
    [ ( m ^. #truthTable . #byteRangeColumnIndex . #unByteRangeColumnIndex,
        FixedColumn byteRange
      ),
      ( m ^. #truthTable . #zeroIndicatorColumnIndex . #unZeroIndicatorColumnIndex,
        FixedColumn zeroIndicator
      )
    ]
  where
    byteRange, zeroIndicator :: [Scalar]
    byteRange =
      fromMaybe (die "byte value out of range of scalar (this is a compiler bug)")
        . integerToScalar
        <$> [0 .. 2 ^ (m ^. #byteDecomposition . #bits . #unBitsPerByte) - 1]
    zeroIndicator = one : replicate (length byteRange - 1) zero

assertStepType ::
  Mapping ->
  Map StepTypeId StepType
assertStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #assertT . #unOf)
    ( StepType
        (PolynomialConstraints [P.minus out i0] 1)
        mempty
        mempty
    )
  where
    i0 = P.var' $ fst (firstTwoInputs m) ^. #unInputColumnIndex
    out = P.var' $ m ^. #output . #unOutputColumnIndex

assertLookupStepType ::
  Mapping ->
  Map StepTypeId StepType
assertLookupStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #assertLookup . #unOf)
    ( StepType
        ( PolynomialConstraints
            [bareLookup' `P.minus` (gate' `P.times` bareLookup')]
            2
        )
        mempty
        mempty
    )
  where
    (i0, i1) = firstTwoInputs m

    gate', bareLookup' :: Polynomial
    gate' = P.var' (i0 ^. #unInputColumnIndex)
    bareLookup' = P.var' (i1 ^. #unInputColumnIndex)

maybeToSet :: Ord a => Maybe a -> Set a
maybeToSet = maybe mempty Set.singleton

getSubexpressionIdSet ::
  SubexpressionIdMapping ->
  Set SubexpressionId
getSubexpressionIdSet m =
  mconcat
    [ maybeToSet ((m ^. #void) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #variables) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #bareLookups) <&> (^. #unBareLookupSubexpressionId)),
      Set.map
        (^. #output . #unOutputSubexpressionId)
        (m ^. #lookupAssertions),
      Set.fromList (Map.elems (m ^. #constants) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #operations) <&> (^. #unOf))
    ]

getSubexpressionLinks ::
  Mapping ->
  Set SubexpressionLink
getSubexpressionLinks m =
  toVoid <> toVarSameCase <> toVarDifferentCase <> toConst <> toOp <> toAssert <> toAssertLookup
  where
    voidEid :: SubexpressionIdOf Void
    voidEid =
      case m ^. #subexpressionIds . #void of
        Just eid -> eid
        Nothing -> die "getSubexpressionLinks: no voidEid (this is a compiler bug)"

    nInputs :: Int
    nInputs = length (m ^. #inputs)

    toVoid, toVarSameCase, toVarDifferentCase, toConst, toOp :: Set SubexpressionLink
    toVoid =
      Set.singleton $
        SubexpressionLink
          (m ^. #stepTypeIds . #voidT . #unOf)
          (replicate nInputs (InputSubexpressionId (voidEid ^. #unOf)))
          (OutputSubexpressionId (voidEid ^. #unOf))

    toVarSameCase =
      Set.fromList $
        [ SubexpressionLink
            stepTypeId
            (replicate nInputs (InputSubexpressionId (voidEid ^. #unOf)))
            (OutputSubexpressionId (eid ^. #unOf))
          | (stepTypeId, eid) <-
              Map.elems $
                Map.intersectionWith
                  (,)
                  (m ^. #stepTypeIds . #loads)
                  (m ^. #subexpressionIds . #variables)
        ]

    toVarDifferentCase =
      Set.fromList $
        [ SubexpressionLink
            (m ^. #stepTypeIds . #loadFromDifferentCase . #unOf)
            (padInputs (InputSubexpressionId <$> [rowIndexEid, stepTypeEid]))
            (OutputSubexpressionId (outEid ^. #unOf))
          | (v, outEid) <- Map.toList $ m ^. #subexpressionIds . #variables,
            let rowIndex = v ^. #rowIndex,
            rowIndex /= 0,
            let rowIndexEid = scalarMapping (rowIndexToScalar rowIndex) ^. #unOf,
            let stepTypeEid = scalarMapping (polyVarStepTypeId (PolynomialVariable (v ^. #colIndex) 0) ^. #unStepTypeId) ^. #unOf
        ]

    rowIndexToScalar :: RowIndex a -> Scalar
    rowIndexToScalar =
      fromMaybe (die "getSubexpressionLinks: could not convert row index to scalar (this is a compiler bug)")
        . integerToScalar
        . intToInteger
        . (^. #getRowIndex)

    polyVarStepTypeId :: PolynomialVariable -> StepTypeId
    polyVarStepTypeId x =
      case Map.lookup x (m ^. #stepTypeIds . #loads) of
        Just sid -> sid
        Nothing -> die "getSubexpressionLinks: polynomial variable mapping lookup failed (this is a compiler bug)"

    scalarMapping :: Scalar -> SubexpressionIdOf Scalar
    scalarMapping x =
      case Map.lookup x (m ^. #subexpressionIds . #constants) of
        Just eid -> eid
        Nothing -> die "getSubexpressionLinks: scalar mapping lookup failed (this is a compiler bug)"

    toConst =
      Set.fromList $
        [ SubexpressionLink
            stepTypeId
            (replicate nInputs (InputSubexpressionId (voidEid ^. #unOf)))
            (OutputSubexpressionId (eid ^. #unOf))
          | (stepTypeId, eid) <-
              Map.elems $
                Map.intersectionWith
                  (,)
                  (m ^. #stepTypeIds . #constants)
                  (m ^. #subexpressionIds . #constants)
        ]

    toOp =
      Set.fromList
        (uncurry operationLink <$> Map.toList (m ^. #subexpressionIds . #operations))

    operationLink :: Operation -> SubexpressionIdOf Operation -> SubexpressionLink
    operationLink =
      \case
        Or' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #or . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))
        OrShortCircuit' x -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #or . #unOf)
            (padInputs (InputSubexpressionId <$> [x]))
            (OutputSubexpressionId (z ^. #unOf))
        Not' x -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #not . #unOf)
            (padInputs [InputSubexpressionId x])
            (OutputSubexpressionId (z ^. #unOf))
        Iff' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #iff . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))
        Plus' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #plus . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))
        TimesAnd' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #timesAnd . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))
        TimesAndShortCircuit' x -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #timesAndShortCircuit . #unOf)
            (padInputs [InputSubexpressionId x])
            (OutputSubexpressionId (z ^. #unOf))
        Equals' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #equals . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))
        LessThan' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #lessThan . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))
        Max' x y -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #maxT . #unOf)
            (padInputs (InputSubexpressionId <$> [x, y]))
            (OutputSubexpressionId (z ^. #unOf))

    padInputs :: [InputSubexpressionId] -> [InputSubexpressionId]
    padInputs xs =
      xs
        <> replicate
          (nInputs - length xs)
          (InputSubexpressionId (voidEid ^. #unOf))

    toAssert =
      Set.fromList $
        [ SubexpressionLink
            (m ^. #stepTypeIds . #assertT . #unOf)
            (padInputs [inEid])
            outEid
          | Assertion inEid outEid <- Set.toList (m ^. #subexpressionIds . #assertions)
        ]

    toAssertLookup =
      Set.fromList $
        [ SubexpressionLink
            (m ^. #stepTypeIds . #assertLookup . #unOf)
            (padInputs [gateEid', bareLookupEid'])
            outEid
          | LookupAssertion bareLookupEid gateEids outEid <-
              Set.toList (m ^. #subexpressionIds . #lookupAssertions),
            let gateEid' =
                  InputSubexpressionId $
                    gateEids ^. #output . #unOutputSubexpressionId,
            let bareLookupEid' =
                  InputSubexpressionId $
                    bareLookupEid ^. #unBareLookupSubexpressionId
        ]

getResultExpressionIds ::
  Mapping ->
  Set ResultExpressionId
getResultExpressionIds m =
  mconcat
    [ Set.map
        (ResultExpressionId . (^. #output . #unOutputSubexpressionId))
        (m ^. #subexpressionIds . #lookupAssertions),
      Set.map
        (ResultExpressionId . (^. #output . #unOutputSubexpressionId))
        (m ^. #subexpressionIds . #assertions)
    ]

maxStepsPerCase ::
  Set SubexpressionId ->
  Scalar
maxStepsPerCase =
  fromMaybe (die "maxStepsPerCase: out of range of scalar (this is a compiler bug)")
    . integerToScalar
    . intToInteger
    . Set.size
