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
    Mapping,
    getMapping,
    getDefaultAdvice,
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger, integerToInt)
import Control.Applicative ((<|>))
import Control.Lens ((<&>), _1, _2, _3)
import Control.Monad (foldM, forM_, mzero, replicateM, when)
import Control.Monad.Trans.State (State, evalState, get, put)
import Data.Either.Extra (mapLeft)
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set
import Data.Text (pack)
import Die (die)
import Halo2.ByteDecomposition (applySign, countBytes, decomposeBytes)
import Halo2.Circuit (getCellMap, getCellMapRows, getLookupTables, getPolynomialVariables, getRowSet, getScalars, lessIndicator)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import qualified Halo2.Types.Argument as LC
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Byte (Byte (Byte))
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Advice, Fixed))
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
import Halo2.Types.RowIndex (RowIndex (RowIndex), RowIndexType (Relative))
import Halo2.Types.Sign (Sign (Negative, Positive))
import OSL.Map (curryMap)
import OSL.Types.Arity (Arity (Arity))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Safe (headMay)
import Stark.Types.Scalar (Scalar, integerToScalar, inverseScalar, normalize, one, scalarToInteger, two, zero)
import Trace.Types (Case (Case), CaseNumberColumnIndex (..), InputColumnIndex (..), InputSubexpressionId (..), NumberOfCases (NumberOfCases), OutputColumnIndex (..), OutputSubexpressionId (..), ResultExpressionId (ResultExpressionId), Statement (Statement), StepIndicatorColumnIndex (..), StepType (StepType), StepTypeId (StepTypeId), StepTypeIdSelectionVector (StepTypeIdSelectionVector), SubexpressionId (SubexpressionId), SubexpressionLink (..), SubexpressionTrace (SubexpressionTrace), Trace (Trace), TraceType (TraceType), Witness (Witness))

newtype LookupCaches = LookupCaches
  { lookupTermCaches ::
      Map
        (Set LookupTableColumn, LC.LookupTableOutputColumn)
        (Map (Map LookupTableColumn Scalar) Scalar)
  }
  deriving (Generic, Show)

getLookupCaches ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Either (ErrorMessage ann) LookupCaches
getLookupCaches ann lc arg =
  LookupCaches . Map.fromList
    <$> mapM
      (\t -> (t,) <$> getLookupTableCache ann lc arg t)
      (Set.toList (getLogicCircuitLookupTables lc))

getLogicCircuitLookupTables ::
  LogicCircuit ->
  Set (Set LookupTableColumn, LC.LookupTableOutputColumn)
getLogicCircuitLookupTables lc =
  mconcat (getConstraintLookupTables . snd <$> lc ^. #gateConstraints . #constraints)

getConstraintLookupTables ::
  LogicConstraint ->
  Set (Set LookupTableColumn, LC.LookupTableOutputColumn)
getConstraintLookupTables =
  \case
    LC.Atom (LC.Equals x y) -> term x <> term y
    LC.Atom (LC.LessThan x y) -> term x <> term y
    LC.Not p -> rec p
    LC.And p q -> rec p <> rec q
    LC.Or p q -> rec p <> rec q
    LC.Iff p q -> rec p <> rec q
    LC.Top -> mempty
    LC.Bottom -> mempty
  where
    rec = getConstraintLookupTables
    term = getTermLookupTables

getTermLookupTables ::
  LC.Term ->
  Set (Set LookupTableColumn, LC.LookupTableOutputColumn)
getTermLookupTables =
  \case
    LC.Var {} -> mempty
    LC.Const {} -> mempty
    LC.Lookup is o ->
      Set.singleton (Set.fromList (snd <$> is), o)
        <> mconcat (rec . (^. #getInputExpression) . fst <$> is)
    LC.Plus x y -> rec x <> rec y
    LC.Times x y -> rec x <> rec y
    LC.Max x y -> rec x <> rec y
    LC.IndLess x y -> rec x <> rec y
  where
    rec = getTermLookupTables

getLookupTableCache ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  (Set LookupTableColumn, LC.LookupTableOutputColumn) ->
  Either (ErrorMessage ann) (Map (Map LookupTableColumn Scalar) Scalar)
getLookupTableCache ann lc arg (inputCols, outputCol) = do
  let rows = getCellMapRows (getRowSet (lc ^. #rowCount) Nothing) (getCellMap arg)
  Map.fromList
    <$> sequence
      [ rowToLookupTableRow r
        | (_, r) <- Map.toList rows
      ]
  where
    rowToLookupTableRow r =
      (,) . Map.fromList
        <$> sequence
          [ maybe
              (Left (ErrorMessage ann "input column not defined"))
              (pure . (inputCol,))
              (Map.lookup (inputCol ^. #unLookupTableColumn) r)
            | inputCol <- Set.toList inputCols
          ]
        <*> maybe
          (Left (ErrorMessage ann "output column not defined"))
          pure
          ( Map.lookup
              ( outputCol
                  ^. #unLookupTableOutputColumn
                    . #unLookupTableColumn
              )
              r
          )

argumentToTrace ::
  ann ->
  BitsPerByte ->
  LogicCircuit ->
  LC.Argument ->
  Either (ErrorMessage ann) Trace
argumentToTrace ann bitsPerByte lc arg = do
  usedCases <- logicCircuitUsedCases ann lc
  voidId <-
    maybe
      (Left (ErrorMessage ann "no void subexpression id"))
      (pure . (^. #unOf))
      (mapping ^. #subexpressionIds . #void)
  Trace
    <$> logicCircuitStatementToTraceStatement ann (arg ^. #statement)
    <*> logicCircuitWitnessToTraceWitness ann (arg ^. #witness)
    <*> ( Map.unionWith (<>) (voidCase usedCases voidId)
            <$> argumentSubexpressionTraces ann lc arg mapping usedCases
        )
  where
    voidCase usedCases voidId =
      curryMap $
        Map.fromList
          [ ( (i, voidId),
              SubexpressionTrace
                zero
                (mapping ^. #stepTypeIds . #voidT . #unOf)
                (getDefaultAdvice mapping)
            )
            | i <- Set.toList usedCases
          ]

    mapping = getMapping bitsPerByte lc

logicCircuitUsedCases ::
  ann ->
  LogicCircuit ->
  Either (ErrorMessage ann) (Set Case)
logicCircuitUsedCases ann lc =
  Set.fromList
    <$> sequence
      [ maybe
          (Left (ErrorMessage ann "case index outside of scalar field"))
          (pure . Case)
          (integerToScalar i)
        | i <- [0 .. scalarToInteger (lc ^. #rowCount . #getRowCount) - 1]
      ]

argumentSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  Set Case ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace))
argumentSubexpressionTraces ann lc arg mapping cases = do
  tables <- getLookupCaches ann lc arg
  Map.unionsWith (<>)
    <$> mapM
      (caseArgumentSubexpressionTraces ann lc arg mapping tables)
      (Set.toList cases)

caseArgumentSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace))
caseArgumentSubexpressionTraces ann lc arg mapping tables c =
  Map.unionWith (<>)
    <$> ( Map.unionsWith (<>)
            <$> mapM
              (fmap (^. _1) . topLevelLogicConstraintSubexpressionTraces ann lc arg mapping tables c)
              ((lc ^. #gateConstraints . #constraints) <&> snd)
        )
    <*> ( Map.unionsWith (<>)
            <$> mapM
              (lookupArgumentSubexpressionTraces ann lc arg mapping tables c)
              (Set.toList (lc ^. #lookupArguments . #getLookupArguments))
        )

getAssertionSubexpressionId ::
  ann ->
  Mapping ->
  InputSubexpressionId ->
  Either (ErrorMessage ann) OutputSubexpressionId
getAssertionSubexpressionId ann mapping inId =
  maybe
    (Left (ErrorMessage ann "assertion subexpression id not found"))
    pure
    (Map.lookup inId (mapping ^. #subexpressionIds . #assertions))

topLevelLogicConstraintSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  LogicConstraint ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
topLevelLogicConstraintSubexpressionTraces ann lc arg mapping caches c p = do
  (m, sId, _) <- logicConstraintSubexpressionTraces ann lc arg mapping caches c p
  OutputSubexpressionId sId' <- getAssertionSubexpressionId ann mapping (InputSubexpressionId sId)
  pure
    ( Map.unionWith (<>) m $
        Map.singleton
          c
          ( Map.singleton
              sId'
              ( SubexpressionTrace
                  zero
                  (mapping ^. #stepTypeIds . #assertT . #unOf)
                  (getDefaultAdvice mapping)
              )
          ),
      sId',
      zero
    )

logicConstraintSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  LogicConstraint ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
logicConstraintSubexpressionTraces ann lc arg mapping tables c =
  \case
    LC.Atom (LC.Equals x y) -> do
      (m0, s0, x') <- term x
      (m1, s1, y') <- term y
      advice <- getByteDecomposition ann lc mapping (normalize (x' Group.- y'))
      s2 <- getOperationSubexpressionId ann mapping (Equals' s0 s1)
      let v = if x' == y' then one else zero
          m2 = Map.singleton c (Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #equals . #unOf) advice))
      pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Atom (LC.LessThan x y) -> do
      (m0, s0, x') <- term x
      (m1, s1, y') <- term y
      advice <- getByteDecomposition ann lc mapping (normalize (x' Group.- y'))
      s2 <- getOperationSubexpressionId ann mapping (LessThan' s0 s1)
      let v = if x' < y' then one else zero
          m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #lessThan . #unOf) advice)
      pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Not p -> do
      (m0, s0, x') <- rec p
      s1 <- getOperationSubexpressionId ann mapping (Not' s0)
      let v = normalize (one Group.- x')
          m1 = Map.singleton c $ Map.singleton s1 (SubexpressionTrace v (mapping ^. #stepTypeIds . #not . #unOf) defaultAdvice)
      pure (Map.unionWith (<>) m0 m1, s1, v)
    t@(LC.And p q) -> do
      (m0, s0, x') <- rec p
      if x' == zero
        then do
          s1 <- getConstraintSubexpressionId ann mapping q
          s2 <- getOperationSubexpressionId ann mapping (TimesAndShortCircuit' s0 s1)
          let m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace zero (mapping ^. #stepTypeIds . #timesAndShortCircuit . #unOf) defaultAdvice)
          pure (Map.unionWith (<>) m0 m2, s2, zero)
        else do
          (m1, s1, y') <- rec q
          s2 <- withTrace t $ getOperationSubexpressionId ann mapping (TimesAnd' s0 s1)
          let v = x' Ring.* y'
              m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #timesAnd . #unOf) defaultAdvice)
          pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    t@(LC.Or p q) -> do
      (m0, s0, x') <- rec p
      if x' == one
        then do
          s1 <- getConstraintSubexpressionId ann mapping q
          s2 <- getOperationSubexpressionId ann mapping (OrShortCircuit' s0 s1)
          let m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace one (mapping ^. #stepTypeIds . #orShortCircuit . #unOf) defaultAdvice)
          pure (Map.unionWith (<>) m0 m2, s2, one)
        else do
          (m1, s1, y') <- rec q
          s2 <- withTrace t (getOperationSubexpressionId ann mapping (Or' s0 s1))
          let v = normalize $ (x' Group.+ y') Group.- (x' Ring.* y')
              m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #or . #unOf) defaultAdvice)
          pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Iff p q -> do
      (m0, s0, x') <- rec p
      (m1, s1, y') <- rec q
      s2 <- getOperationSubexpressionId ann mapping (Iff' s0 s1)
      let v = if x' == y' then one else zero
          m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #iff . #unOf) defaultAdvice)
      pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Top -> do
      sId <- getConstantSubexpressionId ann mapping one
      stId <- getConstantStepTypeId ann mapping one
      pure (Map.singleton c (Map.singleton sId (SubexpressionTrace one stId defaultAdvice)), sId, one)
    LC.Bottom -> do
      sId <- getConstantSubexpressionId ann mapping zero
      stId <- getConstantStepTypeId ann mapping zero
      pure (Map.singleton c (Map.singleton sId (SubexpressionTrace zero stId defaultAdvice)), sId, zero)
  where
    rec = logicConstraintSubexpressionTraces ann lc arg mapping tables c
    term = logicTermSubexpressionTraces ann lc arg mapping tables c
    defaultAdvice = getDefaultAdvice mapping

withTrace :: Show a => a -> Either (ErrorMessage ann) b -> Either (ErrorMessage ann) b
withTrace x = mapLeft (\(ErrorMessage ann' msg) -> ErrorMessage ann' (pack (show x) <> ": " <> msg))

getDefaultAdvice :: Mapping -> Map ColumnIndex Scalar
getDefaultAdvice mapping =
  Map.singleton
    (mapping ^. #byteDecomposition . #sign . #unSignColumnIndex)
    zero
    <> mconcat
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
      bytesSigned = decomposeBytes bitsPerByte x
      signScalar =
        case bytesSigned ^. #sign of
          Positive -> one
          Negative -> zero
      x' = applySign (bytesSigned ^. #sign) x
      bytesUnsigned = decomposeBytes bitsPerByte x'
      numBytes = length (bytesUnsigned ^. #bytes)
  when
    (bytesUnsigned ^. #sign /= Positive)
    (Left (ErrorMessage ann "unsigned byte decomposition is negative (this is a compiler bug)"))
  when
    (length byteCols /= expectedLength)
    (Left (ErrorMessage ann "unexpected byte decomposition mapping length"))
  when
    (numBytes < expectedLength)
    ( Left
        ( ErrorMessage
            ann
            ( "unexpected byte decomposition length: expected "
                <> pack (show expectedLength)
                <> " but got "
                <> pack (show numBytes)
            )
        )
    )
  forM_ (take (numBytes - expectedLength) (bytesUnsigned ^. #bytes)) $ \b ->
    when
      (b /= Byte zero)
      ( Left
          ( ErrorMessage
              ann
              ( "number is out of bounds and will not fit in byte decomposition columns: "
                  <> pack (show (x, bytesSigned))
              )
          )
      )
  pure $
    Map.singleton (signCol ^. #unSignColumnIndex) signScalar
      <> mconcat
        [ Map.fromList
            [ (bCol ^. #unByteColumnIndex, b),
              (tCol ^. #unTruthValueColumnIndex, t)
            ]
          | ((bCol, tCol), (b, t)) <-
              zip
                byteCols
                [ (b, if b == zero then one else zero)
                  | b <-
                      replicate
                        (expectedLength - numBytes)
                        zero
                        <> drop
                          (numBytes - expectedLength)
                          ( (bytesUnsigned ^. #bytes)
                              <&> (^. #unByte)
                          )
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
    Nothing ->
      Left . ErrorMessage ann $
        "operation subexpression id not found: "
          <> pack (show op)

getConstantStepTypeId ::
  ann ->
  Mapping ->
  Scalar ->
  Either (ErrorMessage ann) StepTypeId
getConstantStepTypeId ann mapping x =
  case Map.lookup x (mapping ^. #stepTypeIds . #constants) of
    Just sId -> pure sId
    Nothing -> Left (ErrorMessage ann ("constant step type id not found: " <> pack (show x)))

getConstantSubexpressionId ::
  ann ->
  Mapping ->
  Scalar ->
  Either (ErrorMessage ann) SubexpressionId
getConstantSubexpressionId ann mapping x =
  case Map.lookup x (mapping ^. #subexpressionIds . #constants) of
    Just sId -> pure (sId ^. #unOf)
    Nothing -> Left (ErrorMessage ann "constant subexpression id not found")

getVariableSubexpressionId ::
  ann ->
  Mapping ->
  PolynomialVariable ->
  Either (ErrorMessage ann) SubexpressionId
getVariableSubexpressionId ann mapping x =
  maybe
    (Left (ErrorMessage ann "variable subexpression id not found"))
    (pure . (^. #unOf))
    (Map.lookup x (mapping ^. #subexpressionIds . #variables))

getLookupTermSubexpressionId ::
  ann ->
  Mapping ->
  ([(InputExpression LC.Term, Maybe InputSubexpressionId, LookupTableColumn)], LC.LookupTableOutputColumn) ->
  Either (ErrorMessage ann) SubexpressionId
getLookupTermSubexpressionId ann mapping (is, o) =
  maybe
    (Left (ErrorMessage ann "lookup term subexpression id not found"))
    (pure . (^. #unBareLookupSubexpressionId))
    ( Map.lookup
        ( BareLookupArgument
            ( is
                <> [ ( InputExpression
                         ( LC.Var
                             ( PolynomialVariable
                                 (mapping ^. #output . #unOutputColumnIndex)
                                 (0 :: RowIndex 'Relative)
                             )
                         ),
                       Nothing,
                       o ^. #unLookupTableOutputColumn
                     )
                   ]
            )
        )
        (mapping ^. #subexpressionIds . #bareLookups)
    )

getInputSubexpressionId ::
  ann ->
  Mapping ->
  InputExpression LC.Term ->
  Either (ErrorMessage ann) InputSubexpressionId
getInputSubexpressionId ann mapping (InputExpression x) =
  InputSubexpressionId <$> getTermSubexpressionId ann mapping x

getTermSubexpressionId ::
  ann ->
  Mapping ->
  LC.Term ->
  Either (ErrorMessage ann) SubexpressionId
getTermSubexpressionId ann mapping =
  \case
    LC.Var x -> getVariableSubexpressionId ann mapping x
    LC.Lookup is o -> do
      is' <-
        mapM
          (\(i, c) -> (i,,c) . Just <$> getInputSubexpressionId ann mapping i)
          is
      getLookupTermSubexpressionId ann mapping (is', o)
    LC.Plus x y ->
      op =<< (Plus' <$> rec x <*> rec y)
    LC.Times x y ->
      op =<< (TimesAnd' <$> rec x <*> rec y)
    LC.Max x y ->
      op =<< (Max' <$> rec x <*> rec y)
    LC.IndLess x y ->
      op =<< (LessThan' <$> rec x <*> rec y)
    LC.Const x -> getConstantSubexpressionId ann mapping x
  where
    rec = getTermSubexpressionId ann mapping
    op = getOperationSubexpressionId ann mapping

getConstraintSubexpressionId ::
  ann ->
  Mapping ->
  LogicConstraint ->
  Either (ErrorMessage ann) SubexpressionId
getConstraintSubexpressionId ann mapping =
  \case
    LC.Atom (LC.Equals x y) ->
      op =<< (Equals' <$> term x <*> term y)
    LC.Atom (LC.LessThan x y) ->
      op =<< (LessThan' <$> term x <*> term y)
    LC.Not p -> op . Not' =<< rec p
    LC.And p q -> op =<< (TimesAnd' <$> rec p <*> rec q)
    LC.Or p q -> op =<< (Or' <$> rec p <*> rec q)
    LC.Iff p q -> op =<< (Equals' <$> rec p <*> rec q)
    LC.Top -> const' one
    LC.Bottom -> const' zero
  where
    term = getTermSubexpressionId ann mapping
    op = getOperationSubexpressionId ann mapping
    rec = getConstraintSubexpressionId ann mapping
    const' = getConstantSubexpressionId ann mapping

logicTermSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  LC.Term ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
logicTermSubexpressionTraces ann lc arg mapping tables c =
  \case
    LC.Plus x y -> do
      (m0, s0, x') <- rec x
      (m1, s1, y') <- rec y
      s2 <- getOperationSubexpressionId ann mapping (Plus' s0 s1)
      let v = x' Group.+ y'
          m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #plus . #unOf) defaultAdvice)
      pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Times x y -> do
      (m0, s0, x') <- rec x
      if x' == zero
        then do
          s1 <- getTermSubexpressionId ann mapping y
          s2 <- getOperationSubexpressionId ann mapping (TimesAndShortCircuit' s0 s1)
          let m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace zero (mapping ^. #stepTypeIds . #timesAndShortCircuit . #unOf) defaultAdvice)
          pure (Map.unionWith (<>) m0 m2, s2, zero)
        else do
          (m1, s1, y') <- rec y
          s2 <- getOperationSubexpressionId ann mapping (TimesAnd' s0 s1)
          let v = x' Ring.* y'
              m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #timesAnd . #unOf) defaultAdvice)
          pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Max x y -> do
      (m0, s0, x') <- rec x
      (m1, s1, y') <- rec y
      s2 <- getOperationSubexpressionId ann mapping (Max' s0 s1)
      advice <- getByteDecomposition ann lc mapping (normalize (x' Group.- y'))
      let v = x' `max` y'
          m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #maxT . #unOf) advice)
      pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.IndLess x y -> do
      (m0, s0, x') <- rec x
      (m1, s1, y') <- rec y
      s2 <- getOperationSubexpressionId ann mapping (LessThan' s0 s1)
      advice <- getByteDecomposition ann lc mapping (normalize (x' Group.- y'))
      let v = x' `lessIndicator` y'
          m2 = Map.singleton c $ Map.singleton s2 (SubexpressionTrace v (mapping ^. #stepTypeIds . #lessThan . #unOf) advice)
      pure (Map.unionsWith (<>) [m0, m1, m2], s2, v)
    LC.Const x -> constant x
    LC.Var x -> var x
    LC.Lookup is o -> lkup is o
  where
    rec = logicTermSubexpressionTraces ann lc arg mapping tables c
    var = polyVarSubexpressionTraces ann numCases arg mapping c
    lkup = lookupTermSubexpressionTraces ann lc arg mapping tables c
    constant = constantSubexpressionTraces ann mapping c
    defaultAdvice = getDefaultAdvice mapping
    numCases = NumberOfCases (lc ^. #rowCount . #getRowCount)

constantSubexpressionTraces ::
  ann ->
  Mapping ->
  Case ->
  Scalar ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
constantSubexpressionTraces ann mapping c x = do
  st <- getConstantStepTypeId ann mapping x
  s <- getConstantSubexpressionId ann mapping x
  pure (Map.singleton c (Map.singleton s (SubexpressionTrace x st defaultAdvice)), s, x)
  where
    defaultAdvice = getDefaultAdvice mapping

polyVarSubexpressionTraces ::
  ann ->
  NumberOfCases ->
  LC.Argument ->
  Mapping ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
polyVarSubexpressionTraces ann numCases arg mapping c x =
  if x ^. #rowIndex == 0
    then polyVarSameCaseSubexpressionTraces ann numCases arg mapping c x
    else polyVarDifferentCaseSubexpressionTraces ann numCases arg mapping c x

polyVarSameCaseSubexpressionTraces ::
  ann ->
  NumberOfCases ->
  LC.Argument ->
  Mapping ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
polyVarSameCaseSubexpressionTraces ann numCases arg mapping c x = do
  st <-
    maybe
      (Left (ErrorMessage ann "load step type lookup failed"))
      pure
      (Map.lookup x (mapping ^. #stepTypeIds . #loads))
  sId <-
    maybe
      (Left (ErrorMessage ann "variable subexpression id lookup failed"))
      (pure . (^. #unOf))
      (Map.lookup x (mapping ^. #subexpressionIds . #variables))
  v <- polyVarValue ann numCases arg c x
  pure (Map.singleton c (Map.singleton sId (SubexpressionTrace v st defaultAdvice)), sId, v)
  where
    defaultAdvice = getDefaultAdvice mapping

polyVarValue ::
  ann ->
  NumberOfCases ->
  LC.Argument ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) Scalar
polyVarValue ann (NumberOfCases numCases) arg c v = do
  numCases' <-
    maybe
      (Left (ErrorMessage ann "number of cases exceeds max Int"))
      pure
      (integerToInt (scalarToInteger numCases))
  ri <-
    maybe
      (Left (ErrorMessage ann "row index exceeds max Int"))
      pure
      (integerToInt (scalarToInteger (c ^. #unCase)))
  let ref =
        CellReference
          (v ^. #colIndex)
          ( RowIndex
              ( (ri + (v ^. #rowIndex . #getRowIndex))
                  `mod` numCases'
              )
          )
  case Map.lookup ref (arg ^. #statement . #unStatement) of
    Just x -> pure x
    Nothing ->
      maybe
        ( Left
            ( ErrorMessage
                ann
                ("variable not defined: " <> pack (show (c, v)))
            )
        )
        pure
        (Map.lookup ref (arg ^. #witness . #unWitness))

polyVarDifferentCaseSubexpressionTraces ::
  ann ->
  NumberOfCases ->
  LC.Argument ->
  Mapping ->
  Case ->
  PolynomialVariable ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
polyVarDifferentCaseSubexpressionTraces ann numCases arg mapping c x = do
  (m0, _, _) <- constant c (rowIndexToScalar (x ^. #rowIndex))
  st <-
    maybe
      (Left (ErrorMessage ann "step type id lookup failed"))
      pure
      ( Map.lookup
          (x ^. #colIndex)
          (mapping ^. #stepTypeIds . #loadFromDifferentCase)
      )
  sId <-
    maybe
      (Left (ErrorMessage ann "variable subexpression id lookup failed"))
      (pure . (^. #unOf))
      (Map.lookup x (mapping ^. #subexpressionIds . #variables))
  v <- polyVarValue ann numCases arg c x
  (m2, _, _) <-
    polyVarSameCaseSubexpressionTraces
      ann
      numCases
      arg
      mapping
      (Case a)
      (PolynomialVariable (x ^. #colIndex) 0)
  let m3 = Map.singleton c $ Map.singleton sId (SubexpressionTrace v st advice)
  pure (Map.unionsWith (<>) [m0, m2, m3], sId, v)
  where
    constant = constantSubexpressionTraces ann mapping
    defaultAdvice = getDefaultAdvice mapping
    ai = firstAdviceColumn mapping
    di = secondAdviceColumn mapping
    n = numCases ^. #unNumberOfCases
    r = rowIndexToScalar (x ^. #rowIndex)
    a =
      normalize $
        fromMaybe
          (die "polyVarDifferentCaseSubexpressionTraces: offset row index mod row count out of range of scalar (this is a compiler bug")
          (integerToScalar (scalarToInteger (normalize ((c ^. #unCase) Group.+ r)) `mod` scalarToInteger n))
    divZero = "polyVarDifferentCaseSubexpressionTraces: division by zero"
    d = normalize $ normalize (((c ^. #unCase) Group.+ r) Group.- a) Ring.* fromMaybe (die divZero) (inverseScalar n)
    specialAdvice = Map.fromList [(ai, a), (di, d)]
    advice = specialAdvice <> defaultAdvice

    rowIndexToScalar :: RowIndex a -> Scalar
    rowIndexToScalar =
      fromMaybe (die "polyVarDifferentCaseSubexpressionTraces: could not convert row index to scalar (this is a compiler bug)")
        . integerToScalar
        . intToInteger
        . (^. #getRowIndex)

lookupTermSubexpressionTraces ::
  ann ->
  LogicCircuit ->
  LC.Argument ->
  Mapping ->
  LookupCaches ->
  Case ->
  [(InputExpression LC.Term, LookupTableColumn)] ->
  LC.LookupTableOutputColumn ->
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace), SubexpressionId, Scalar)
lookupTermSubexpressionTraces ann lc arg mapping tables c lookupArg outCol = do
  inputs' <-
    Map.fromList
      . zip ((^. _2) <$> lookupArg)
      <$> mapM (term . (^. #getInputExpression) . (^. _1)) lookupArg
  let lookupTerm = (Set.fromList ((^. _2) <$> lookupArg), outCol)
      lookupInputs = inputs' <&> (^. _2)
  lookupCache <-
    maybe
      ( Left
          ( ErrorMessage
              ann
              ("lookup cache lookup failed: " <> pack (show lookupTerm))
          )
      )
      pure
      ( Map.lookup
          lookupTerm
          (tables ^. #lookupTermCaches)
      )
  v <-
    maybe
      ( Left
          ( ErrorMessage
              ann
              ("lookup term lookup failed: " <> pack (show (lookupTerm, lookupInputs)))
          )
      )
      pure
      (Map.lookup (inputs' <&> (^. _3)) lookupCache)
  st <-
    maybe
      (Left (ErrorMessage ann "step type lookup failed"))
      pure
      ( Map.lookup
          ( LookupTable
              ( ((^. _2) <$> lookupArg)
                  <> [outCol ^. #unLookupTableOutputColumn]
              )
          )
          (mapping ^. #stepTypeIds . #lookupTables)
      )
  sId <-
    maybe
      (Left (ErrorMessage ann "lookup subexpression id lookup failed"))
      (pure . (^. #unBareLookupSubexpressionId))
      ( Map.lookup
          ( BareLookupArgument
              ( zipWith
                  (\(ie, col) eid -> (ie, Just eid, col))
                  lookupArg
                  (Map.elems (inputs' <&> InputSubexpressionId . (^. _2)))
                  <> [ ( InputExpression
                           ( LC.Var
                               ( PolynomialVariable
                                   (mapping ^. #output . #unOutputColumnIndex)
                                   (0 :: RowIndex 'Relative)
                               )
                           ),
                         Nothing,
                         outCol ^. #unLookupTableOutputColumn
                       )
                     ]
              )
          )
          (mapping ^. #subexpressionIds . #bareLookups)
      )
  let ms = inputs' <&> (^. _1)
      m' = Map.singleton c $ Map.singleton sId (SubexpressionTrace v st defaultAdvice)
  pure (Map.unionWith (<>) m' (Map.unionsWith (<>) (Map.elems ms)), sId, v)
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
  Either (ErrorMessage ann) (Map Case (Map SubexpressionId SubexpressionTrace))
lookupArgumentSubexpressionTraces ann _ _ _ _ _ _ =
  Left (ErrorMessage ann "unsupported: lookup argument in logic circuit being translated to a trace type")

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
  Map.fromList
    <$> sequence
      [ (,)
          <$> ( (,col) . Case
                  <$> maybe
                    (Left (ErrorMessage ann "row index out of range of scalar field"))
                    pure
                    (integerToScalar (intToInteger (row ^. #getRowIndex)))
              )
          <*> pure x
        | (CellReference col row, x) <- Map.toList cellMap
      ]

logicCircuitToTraceType ::
  BitsPerByte ->
  LogicCircuit ->
  TraceType
logicCircuitToTraceType bitsPerByte c =
  TraceType
    colTypes'
    (c ^. #equalityConstrainableColumns)
    (c ^. #equalityConstraints)
    ( FixedValues
        . fmap
          ( FixedColumn
              . Map.mapKeys rowIndexToCase
              . (^. #unFixedColumn)
          )
        $ (c ^. #fixedValues . #getFixedValues)
    )
    stepTypes
    subexprs
    (getSubexpressionLinksMap mapping)
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

    rowIndexToCase =
      maybe
        (die "Trace.FromLogicCircuit.logicCircuitToTraceType: could not convert row index to case")
        Case
        . integerToScalar
        . intToInteger
        . (^. #getRowIndex)

-- TODO: let the columns be reused where possible
data Mapping = Mapping
  { caseNumber :: CaseNumberColumnIndex,
    stepType :: StepTypeIdSelectionVector,
    stepIndicator :: StepIndicatorColumnIndex,
    inputs :: [InputColumnIndex],
    output :: OutputColumnIndex,
    byteDecomposition :: ByteDecompositionMapping,
    truthTable :: TruthTableColumnIndices,
    stepTypeIds :: StepTypeIdMapping,
    subexpressionIds :: SubexpressionIdMapping
  }
  deriving (Generic, Show)

data ByteDecompositionMapping = ByteDecompositionMapping
  { bits :: BitsPerByte,
    sign :: SignColumnIndex,
    bytes :: [(ByteColumnIndex, TruthValueColumnIndex)] -- most significant first
  }
  deriving (Generic, Show)

newtype TruthValueColumnIndex = TruthValueColumnIndex
  {unTruthValueColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

newtype SignColumnIndex = SignColumnIndex {unSignColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

newtype ByteColumnIndex = ByteColumnIndex {unByteColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

newtype ByteRangeColumnIndex = ByteRangeColumnIndex
  {unByteRangeColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

newtype ZeroIndicatorColumnIndex = ZeroIndicatorColumnIndex
  {unZeroIndicatorColumnIndex :: ColumnIndex}
  deriving (Generic, Show)

data TruthTableColumnIndices = TruthTableColumnIndices
  { byteRangeColumnIndex :: ByteRangeColumnIndex,
    zeroIndicatorColumnIndex :: ZeroIndicatorColumnIndex
  }
  deriving (Generic, Show)

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
  | LoadFromDifferentCase
  deriving (Show)

type StepTypeIdOf :: Operator -> Type
newtype StepTypeIdOf a = StepTypeIdOf {unOf :: StepTypeId}
  deriving (Generic, Show)

newtype LookupTable = LookupTable {unLookupTable :: [LookupTableColumn]}
  deriving (Eq, Ord, Generic, Show)

newtype BareLookupArgument = BareLookupArgument
  { getBareLookupArgument ::
      [(InputExpression LC.Term, Maybe InputSubexpressionId, LookupTableColumn)]
  }
  deriving (Eq, Ord, Generic, Show)

data StepTypeIdMapping = StepTypeIdMapping
  { voidT :: StepTypeIdOf VoidT,
    loads :: Map PolynomialVariable StepTypeId,
    loadFromDifferentCase :: Map ColumnIndex StepTypeId,
    lookupTables :: Map LookupTable StepTypeId,
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
    assertT :: StepTypeIdOf AssertT
  }
  deriving (Generic, Show)

type SubexpressionIdOf :: Type -> Type
newtype SubexpressionIdOf a = SubexpressionIdOf {unOf :: SubexpressionId}
  deriving (Generic, Show)

type Void :: Type
data Void

data Operation
  = Or' SubexpressionId SubexpressionId
  | -- The short circuit operations do not actually take the second subexpression
    -- argument as an input; but it has to be present, because there can be more than
    -- one subexpression with the same operator and the same left hand side but
    -- different right hand sides. Those subexpressions need to be mapped to distinct
    -- ids, and therefore they need to be treated as distinct operations.
    OrShortCircuit' SubexpressionId SubexpressionId
  | Not' SubexpressionId
  | Iff' SubexpressionId SubexpressionId
  | Plus' SubexpressionId SubexpressionId
  | TimesAnd' SubexpressionId SubexpressionId
  | TimesAndShortCircuit' SubexpressionId SubexpressionId
  | Equals' SubexpressionId SubexpressionId
  | LessThan' SubexpressionId SubexpressionId
  | Max' SubexpressionId SubexpressionId
  deriving (Eq, Ord, Show)

newtype BareLookupSubexpressionId = BareLookupSubexpressionId {unBareLookupSubexpressionId :: SubexpressionId}
  deriving (Eq, Ord, Generic, Show)

data GateSubexpressionIds = GateSubexpressionIds
  { input :: InputSubexpressionId,
    output :: OutputSubexpressionId
  }
  deriving (Eq, Ord, Generic, Show)

data SubexpressionIdMapping = SubexpressionIdMapping
  { void :: Maybe (SubexpressionIdOf Void),
    assertions :: Map InputSubexpressionId OutputSubexpressionId,
    variables :: Map PolynomialVariable (SubexpressionIdOf PolynomialVariable),
    bareLookups :: Map BareLookupArgument BareLookupSubexpressionId,
    constants :: Map Scalar (SubexpressionIdOf Scalar),
    operations :: Map Operation (SubexpressionIdOf Operation)
  }
  deriving (Generic, Show)

instance Semigroup SubexpressionIdMapping where
  (SubexpressionIdMapping b c d e f g) <> (SubexpressionIdMapping j k l m n o) =
    SubexpressionIdMapping
      (b <|> j)
      (c <> k)
      (d <> l)
      (e <> m)
      (f <> n)
      (g <> o)

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

    resetSid :: State S ()
    resetSid = do
      S i _ k <- get
      put (S i 0 k)

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
      stc <-
        StepTypeIdSelectionVector . Map.fromList
          <$> replicateM
            (countStepTypes c)
            ((,) <$> nextSid <*> nextCol)
      resetSid
      sic <- StepIndicatorColumnIndex <$> nextCol
      ins <-
        replicateM
          (getStepArity c ^. #unArity)
          (InputColumnIndex <$> nextCol)
      out <- OutputColumnIndex <$> nextCol
      voidStepTypeMapping <- nextSid'
      polyVarsZeroOffsetMapping <-
        Map.fromList . zip polyVarsZeroOffset
          <$> replicateM (length polyVarsZeroOffset) nextSid
      let scalars' = Set.toList $ getAllScalars c
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
        <*> ( StepTypeIdMapping voidStepTypeMapping polyVarsZeroOffsetMapping
                <$> ( Map.fromList
                        <$> sequence
                          [ (ci,) <$> nextSid
                            | ci <-
                                Set.toList . Set.fromList
                                  . fmap (^. #colIndex)
                                  $ filter
                                    ((/= 0) . (^. #rowIndex))
                                    polyVars
                          ]
                    )
                <*> ( Map.fromList . zip lookupTables'
                        <$> replicateM (length lookupTables') nextSid
                    )
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
                    <*> pure mempty
                    <*> ( Map.fromList . zip scalars'
                            <$> replicateM (length scalars') nextEid'
                        )
                    <*> pure mempty
                traverseLookupArguments out (c ^. #lookupArguments)
                  =<< traverseLogicConstraints out m0 (c ^. #gateConstraints)
            )

    traverseLookupArguments :: OutputColumnIndex -> LookupArguments LC.Term -> SubexpressionIdMapping -> State S SubexpressionIdMapping
    traverseLookupArguments _out args m' =
      foldM traverseLookupArgument m' (args ^. #getLookupArguments)

    traverseLookupArgument :: SubexpressionIdMapping -> LookupArgument LC.Term -> State S SubexpressionIdMapping
    traverseLookupArgument _ _ =
      die "unsupported: converting a logic circuit containing a lookup argument to a trace type"

    traverseBareLookupArgument :: OutputColumnIndex -> SubexpressionIdMapping -> BareLookupArgument -> State S (BareLookupSubexpressionId, SubexpressionIdMapping)
    traverseBareLookupArgument out m' arg = do
      m'' <-
        foldM
          (\m'' e -> snd <$> traverseTerm out m'' (e ^. _1 . #getInputExpression))
          m'
          (arg ^. #getBareLookupArgument)
      case Map.lookup arg (m' ^. #bareLookups) of
        Just bareLookupId -> pure (bareLookupId, m'')
        Nothing -> do
          eid <- BareLookupSubexpressionId <$> nextEid
          let m''' = m'' <> SubexpressionIdMapping mzero mempty mempty (Map.singleton arg eid) mempty mempty
          pure (eid, m''')

    traverseLogicConstraints :: OutputColumnIndex -> SubexpressionIdMapping -> LogicConstraints -> State S SubexpressionIdMapping
    traverseLogicConstraints out m' lcs =
      foldM (traverseAssertion out) m' (snd <$> (lcs ^. #constraints))

    traverseAssertion :: OutputColumnIndex -> SubexpressionIdMapping -> LogicConstraint -> State S SubexpressionIdMapping
    traverseAssertion out m' lc = do
      (inEid, m'') <- traverseConstraint out m' lc
      outEid <- OutputSubexpressionId <$> nextEid
      pure (addAssertion m'' (InputSubexpressionId inEid, outEid))

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
          pure $ addOp m'''' (TimesAndShortCircuit' xId yId) (SubexpressionIdOf zId)
        LC.Or x y -> do
          (xId, m'') <- traverseConstraint out m' x
          (yId, m''') <- traverseConstraint out m'' y
          (zId, m'''') <- addOp m''' (Or' xId yId) <$> nextEid'
          pure $ addOp m'''' (OrShortCircuit' xId yId) (SubexpressionIdOf zId)
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
      -- The same subexpression can occur in multiple places, and we don't want to
      -- change its id because that would invalidate references to the same subexpression
      -- in other operations.
      case Map.lookup op (m' ^. #operations) of
        Just opId' -> (opId' ^. #unOf, m')
        Nothing -> (opId ^. #unOf, SubexpressionIdMapping mzero mempty mempty mempty mempty (Map.singleton op opId) <> m')

    addAssertion ::
      SubexpressionIdMapping ->
      (InputSubexpressionId, OutputSubexpressionId) ->
      SubexpressionIdMapping
    addAssertion m' (i, o) =
      m' <> SubexpressionIdMapping mzero (Map.singleton i o) mempty mempty mempty mempty

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
          (m'', inIds) <-
            foldM
              ( \(m'', inIds) (InputExpression e, _col) -> do
                  (eid, m''') <- traverseTerm out m'' e
                  pure (m''', inIds <> [InputSubexpressionId eid])
              )
              (m', mempty)
              is
          (eid, m''') <-
            traverseBareLookupArgument out m'' . BareLookupArgument $
              zipWith (\(i, col) inId -> (i, Just inId, col)) is inIds
                <> [ ( InputExpression (LC.Var (PolynomialVariable (out ^. #unOutputColumnIndex) 0)),
                       Nothing,
                       o
                     )
                   ]
          pure (eid ^. #unBareLookupSubexpressionId, m''')
        LC.Const x -> pure (constantEid m' x, m')
        LC.Plus x y -> do
          (xEid, m'') <- traverseTerm out m' x
          (yEid, m''') <- traverseTerm out m'' y
          addOp m''' (Plus' xEid yEid) <$> nextEid'
        LC.Times x y -> do
          (xEid, m'') <- traverseTerm out m' x
          (yEid, m''') <- traverseTerm out m'' y
          (zEid, m'''') <- addOp m''' (TimesAnd' xEid yEid) <$> nextEid'
          pure $ addOp m'''' (TimesAndShortCircuit' xEid yEid) (SubexpressionIdOf zEid)
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

getAllScalars :: LogicCircuit -> Set Scalar
getAllScalars c =
  mconcat
    [ getScalars c,
      Set.fromList [0, 1],
      Set.map (rowIndexToScalar . (^. #rowIndex)) (getPolynomialVariables c)
    ]
  where
    rowIndexToScalar :: RowIndex a -> Scalar
    rowIndexToScalar =
      fromMaybe (die "getAllScalars: could not convert row index to scalar (this is a compiler bug)")
        . integerToScalar
        . intToInteger
        . (^. #getRowIndex)

getColumnTypes :: LogicCircuit -> Mapping -> ColumnTypes
getColumnTypes c mapping =
  (c ^. #columnTypes)
    <> ( ColumnTypes . Map.fromList $
           ((,Advice) <$> getAdviceMappingIndices mapping)
             <> ((,Fixed) <$> getFixedMappingIndices mapping)
       )

getFixedMappingIndices :: Mapping -> [ColumnIndex]
getFixedMappingIndices m =
  [ m ^. #caseNumber . #unCaseNumberColumnIndex,
    m ^. #truthTable . #byteRangeColumnIndex . #unByteRangeColumnIndex,
    m ^. #truthTable . #zeroIndicatorColumnIndex . #unZeroIndicatorColumnIndex
  ]

getAdviceMappingIndices :: Mapping -> [ColumnIndex]
getAdviceMappingIndices m =
  [ m ^. #caseNumber . #unCaseNumberColumnIndex,
    m ^. #stepIndicator . #unStepIndicatorColumnIndex
  ]
    <> Map.elems (m ^. #stepType . #unStepTypeIdSelectionVector)
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

getStepTypes ::
  BitsPerByte ->
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType
getStepTypes bitsPerByte c m =
  mconcat
    [ loadStepTypes c m,
      bareLookupStepTypes m,
      constantStepTypes m,
      operatorStepTypes bitsPerByte c m,
      assertStepType m
    ]

loadStepTypes ::
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType
loadStepTypes c m =
  Map.fromList $
    [ ( stId,
        loadFromDifferentCaseStepType numCases m stId ci
      )
      | (ci, stId) <-
          Map.toList (m ^. #stepTypeIds . #loadFromDifferentCase)
    ]
      <> catMaybes
        [ (sId,) <$> loadStepType m x
          | (x, sId) <- Map.toList (m ^. #stepTypeIds . #loads)
        ]
  where
    numCases = NumberOfCases $ c ^. #rowCount . #getRowCount

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
    label
    ( PolynomialConstraints
        [ ( label,
            P.minus
              (P.var' i)
              (P.var' (m ^. #output . #unOutputColumnIndex))
          )
        ]
        1
    )
    mempty
    mempty
  where
    label = "loadFromSameCase(" <> Label (show i) <> ")"

loadFromDifferentCaseStepType ::
  NumberOfCases ->
  Mapping ->
  StepTypeId ->
  ColumnIndex ->
  StepType
loadFromDifferentCaseStepType numCases m stId vi =
  StepType
    (Label $ "loadFromDifferentCase(" <> show vi <> ")")
    ( PolynomialConstraints
        [ ( Label $ "loadFromDifferentCase1(" <> show vi <> ")",
            d `P.times` ((d `P.plus` P.one) `P.times` (d `P.minus` P.one))
          ),
          ( Label $ "loadFromDifferentCase2(" <> show vi <> ")",
            a `P.minus` (b `P.plus` (d `P.times` P.constant n))
          )
        ]
        3
    )
    ( LookupArguments . Set.singleton $
        LookupArgument
          (Label $ "loadFromDifferentCase(" <> show vi <> ")")
          P.zero
          [(o, os), (c, cs), (t, ts)]
    )
    mempty
  where
    (i0, _i1) = firstTwoInputs m
    i = P.var' (m ^. #caseNumber . #unCaseNumberColumnIndex)
    r = P.var' (i0 ^. #unInputColumnIndex)
    b = i `P.plus` r
    a = P.var' (firstAdviceColumn m)
    d = P.var' (secondAdviceColumn m)
    n = numCases ^. #unNumberOfCases

    o, c, t :: InputExpression Polynomial
    o = InputExpression (P.var' (m ^. #output . #unOutputColumnIndex))
    c = InputExpression a
    t = InputExpression P.one

    os, cs, ts :: LookupTableColumn
    os = LookupTableColumn (m ^. #output . #unOutputColumnIndex)
    cs = LookupTableColumn (m ^. #caseNumber . #unCaseNumberColumnIndex)
    ts =
      maybe
        (die ("loadFromDifferentCaseStepType: could not look up selection vector column: " <> pack (show stId)))
        LookupTableColumn
        ( Map.lookup
            (PolynomialVariable vi 0)
            (m ^. #stepTypeIds . #loads)
            >>= (`Map.lookup` (m ^. #stepType . #unStepTypeIdSelectionVector))
        )

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
    ("lookup(" <> Label (show t) <> ")")
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
    ("constant(" <> Label (show x) <> ")")
    ( PolynomialConstraints
        [ ( "constant",
            P.minus
              (P.constant x)
              (P.var' (m ^. #output . #unOutputColumnIndex))
          )
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

-- Steal an advice column from the byte decomposition mapping
-- for any other purpose (on steps which do not use byte decomposition).
firstAdviceColumn,
  secondAdviceColumn ::
    Mapping ->
    ColumnIndex
firstAdviceColumn mapping =
  mapping ^. #byteDecomposition . #sign . #unSignColumnIndex
secondAdviceColumn mapping =
  maybe
    (die "no bytes in byte decomposition (this is supposed to be impossible)")
    (^. _1 . #unByteColumnIndex)
    (headMay (mapping ^. #byteDecomposition . #bytes))

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
        "plus"
        ( PolynomialConstraints
            [ ( "plus",
                P.minus
                  (P.var' (m ^. #output . #unOutputColumnIndex))
                  ( P.plus
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
timesStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #timesAnd . #unOf)
    ( StepType
        "timesAnd"
        ( PolynomialConstraints
            [ ( "timesAnd",
                P.minus
                  (P.var' (m ^. #output . #unOutputColumnIndex))
                  ( P.times
                      (P.var' (i0 ^. #unInputColumnIndex))
                      (P.var' (i1 ^. #unInputColumnIndex))
                  )
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
        "timesAndShortCircuit"
        ( PolynomialConstraints
            [ ("timesAndShortCircuit1", P.var' (m ^. #output . #unOutputColumnIndex)),
              ("timesAndShortCircuit2", P.var' (i0 ^. #unInputColumnIndex))
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
        "or"
        ( PolynomialConstraints
            [ ( "or",
                P.minus
                  (P.var' (m ^. #output . #unOutputColumnIndex))
                  (P.plus v0 (P.minus v1 (P.times v0 v1)))
              )
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
        "orShortCircuit"
        ( PolynomialConstraints
            [ ("orShortCircuit1", P.minus P.one (P.var' (m ^. #output . #unOutputColumnIndex))),
              ("orShortCircuit2", P.minus P.one (P.var' (i0 ^. #unInputColumnIndex)))
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
        "not"
        ( PolynomialConstraints
            [ ( "not",
                P.minus
                  (P.var' (m ^. #output . #unOutputColumnIndex))
                  (P.minus P.one (P.var' (i0 ^. #unInputColumnIndex)))
              )
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
        "iff"
        ( PolynomialConstraints
            [ ( "iff",
                P.minus
                  (P.var' (m ^. #output . #unOutputColumnIndex))
                  ( P.minus
                      P.one
                      ( P.minus
                          (P.var' (i0 ^. #unInputColumnIndex))
                          (P.var' (i1 ^. #unInputColumnIndex))
                      )
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
  Map.singleton
    (m ^. #stepTypeIds . #voidT . #unOf)
    (StepType "void" mempty mempty mempty)

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
            "equals"
            ( PolynomialConstraints
                [ ("equalsResultIsBinary", result `P.times` (result `P.minus` P.one)),
                  ("equalsResultIsTruthful", result `P.times` foldl' P.plus P.zero ((P.one `P.minus`) <$> truthVars))
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
            "lessThan"
            ( PolynomialConstraints
                [ ("lessThanResultIsBinary", result `P.times` (result `P.minus` P.one)),
                  ( "lessThanResultTrue",
                    (P.one `P.minus` result)
                      `P.times` ( (P.one `P.minus` sign')
                                    `P.times` foldl' P.plus P.zero truthVars
                                )
                  ),
                  ( "lessThanResultFalse",
                    result
                      `P.times` ( P.one
                                    `P.minus` foldl'
                                      P.times
                                      P.one
                                      [P.one `P.minus` v | v <- truthVars]
                                )
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
            "max"
            ( PolynomialConstraints
                [ ( "max",
                    P.var' out
                      `P.minus` ( (P.var' i1 `P.times` lessInd)
                                    `P.plus` (P.var' i0 `P.times` (P.one `P.minus` lessInd))
                                )
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
    "byteDecompositionCheck"
    ( PolynomialConstraints
        [ ( "byteRecomposition",
            (v0 `P.minus` v1)
              `P.minus` ( ((P.constant two `P.times` s) `P.minus` P.one)
                            `P.times` foldl'
                              P.plus
                              P.zero
                              (zipWith P.times byteCoefs byteVars)
                        )
          ),
          ("signIsBinary", s `P.times` (s `P.minus` P.one))
        ]
        (PolynomialDegreeBound 2)
    )
    (byteRangeAndTruthChecks m)
    (truthTables rc m)
  where
    (i0, i1) = firstTwoInputs m
    v0 = P.var' (i0 ^. #unInputColumnIndex)
    v1 = P.var' (i1 ^. #unInputColumnIndex)
    s = P.var' (m ^. #byteDecomposition . #sign . #unSignColumnIndex)
    rc = c ^. #rowCount

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
  RowCount ->
  Mapping ->
  FixedValues Case
truthTables (RowCount n) m =
  FixedValues . Map.fromList $
    [ ( m ^. #truthTable . #byteRangeColumnIndex . #unByteRangeColumnIndex,
        byteRange
      ),
      ( m ^. #truthTable . #zeroIndicatorColumnIndex . #unZeroIndicatorColumnIndex,
        zeroIndicator
      )
    ]
  where
    b, n' :: Int
    b = 2 ^ (m ^. #byteDecomposition . #bits . #unBitsPerByte)
    n' =
      fromMaybe
        (die "Trace.FromLogicCircuit.truthTables: row count out of range of Int")
        (integerToInt (scalarToInteger n))

    byteRange, zeroIndicator :: FixedColumn Case
    byteRange =
      FixedColumn . Map.fromList
        . zip cases
        $ fromMaybe (die "Trace.FromLogicCircuit.truthTables: byte value out of range of scalar (this is a compiler bug)")
          . integerToScalar
          . intToInteger
          <$> ( [0 .. b - 1]
                  <> replicate (n' - b) (b - 1)
              )
    zeroIndicator =
      FixedColumn . Map.fromList
        . zip cases
        $ one : replicate (n' - 1) 0

    cases :: [Case]
    cases =
      maybe
        (die "Trace.FromLogicCircuit.truthTables: case number out of range of Int")
        Case
        . integerToScalar
        <$> [0 .. scalarToInteger n]

assertStepType ::
  Mapping ->
  Map StepTypeId StepType
assertStepType m =
  Map.singleton
    (m ^. #stepTypeIds . #assertT . #unOf)
    ( StepType
        "assert"
        (PolynomialConstraints [("assert", P.minus P.one i0)] 1)
        mempty
        mempty
    )
  where
    i0 = P.var' $ fst (firstTwoInputs m) ^. #unInputColumnIndex

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
      Set.fromList (Map.elems (m ^. #constants) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #operations) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #assertions) <&> (^. #unOutputSubexpressionId))
    ]

getSubexpressionLinksMap ::
  Mapping ->
  Map (StepTypeId, OutputSubexpressionId) [InputSubexpressionId]
getSubexpressionLinksMap m =
  Map.fromList
    [ ((st, o), is)
      | SubexpressionLink st is o <- Set.toList (getSubexpressionLinks m)
    ]

getSubexpressionLinks ::
  Mapping ->
  Set SubexpressionLink
getSubexpressionLinks m =
  mconcat
    [ toVoid,
      toVarSameCase,
      toVarDifferentCase,
      toConst,
      toOp,
      toAssert,
      toBareLookup
    ]
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
            stepTypeId
            (padInputs (InputSubexpressionId <$> [rowIndexEid]))
            (OutputSubexpressionId (outEid ^. #unOf))
          | (v, outEid) <- Map.toList $ m ^. #subexpressionIds . #variables,
            let rowIndex = v ^. #rowIndex,
            rowIndex /= 0,
            let stepTypeId = polyVarStepTypeId v,
            let rowIndexEid = scalarMapping (rowIndexToScalar rowIndex) ^. #unOf
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
        Nothing ->
          case Map.lookup
            (x ^. #colIndex)
            (m ^. #stepTypeIds . #loadFromDifferentCase) of
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
        OrShortCircuit' x _ -> \z ->
          SubexpressionLink
            (m ^. #stepTypeIds . #orShortCircuit . #unOf)
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
        TimesAndShortCircuit' x _ -> \z ->
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
          | (inEid, outEid) <- Map.toList (m ^. #subexpressionIds . #assertions)
        ]

    toBareLookup =
      Set.fromList $
        [ SubexpressionLink
            (getLookupStepTypeId arg)
            ( padInputs
                ( catMaybes ((arg ^. #getBareLookupArgument) <&> (^. _2))
                    <> [InputSubexpressionId outEid]
                )
            )
            (OutputSubexpressionId outEid)
          | (arg, BareLookupSubexpressionId outEid) <-
              Map.toList (m ^. #subexpressionIds . #bareLookups)
        ]

    getLookupStepTypeId :: BareLookupArgument -> StepTypeId
    getLookupStepTypeId (BareLookupArgument arg) =
      fromMaybe
        (die "getSubexpressionLinks: lookup step type id not found (this is a compiler bug)")
        (Map.lookup (LookupTable (arg <&> (^. _3))) (m ^. #stepTypeIds . #lookupTables))

getResultExpressionIds ::
  Mapping ->
  Set ResultExpressionId
getResultExpressionIds m =
  Set.fromList $
    ResultExpressionId . (^. #unOutputSubexpressionId)
      <$> Map.elems (m ^. #subexpressionIds . #assertions)

maxStepsPerCase ::
  Set SubexpressionId ->
  Scalar
maxStepsPerCase =
  fromMaybe (die "maxStepsPerCase: out of range of scalar (this is a compiler bug)")
    . integerToScalar
    . intToInteger
    . Set.size

countStepTypes ::
  LogicCircuit ->
  Int
countStepTypes c =
  countLoadStepTypes
    + countBareLookupStepTypes
    + countConstantStepTypes
    + 12
  where
    countBareLookupStepTypes =
      Set.size (Set.map snd (getLookupTables @LogicCircuit @LC.Term c))

    countConstantStepTypes =
      Set.size (getAllScalars c)

    countLoadStepTypes =
      countLoadFromSameCaseStepTypes
        + countLoadFromDifferentCaseStepTypes

    countLoadFromSameCaseStepTypes =
      Set.size (Set.map (^. #colIndex) polyVars)

    countLoadFromDifferentCaseStepTypes =
      Set.size (Set.map (^. #colIndex) (Set.filter ((/= 0) . (^. #rowIndex)) polyVars))

    polyVars = getPolynomialVariables c
