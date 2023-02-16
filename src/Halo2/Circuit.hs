{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unused-imports -Wno-unused-matches #-}

module Halo2.Circuit
  ( HasPolynomialVariables (getPolynomialVariables),
    HasScalars (getScalars),
    HasLookupArguments (getLookupArguments),
    fixedValuesToCellMap,
    getLookupTables,
    HasEvaluate (evaluate),
    lessIndicator,
    rowsToCellMap,
    getCellMapRows,
    getCellMap,
    getRowSet,
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (intToInteger, integerToInt)
import Control.Applicative (liftA2)
import Control.Arrow (first)
import Control.Lens ((<&>))
import Control.Monad.Extra (allM, andM, when, (&&^), (||^))
import Data.Either.Extra (mapLeft)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text (pack)
import Data.Tuple.Extra (second, swap, uncurry3)
import Die (die)
import Halo2.Polynomial (degree)
import Halo2.Prelude
import Halo2.Types.Argument (Argument)
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.Circuit (Circuit, LogicCircuit)
import Halo2.Types.Coefficient (Coefficient (Coefficient, getCoefficient))
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType (Advice, Fixed, Instance))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns (EqualityConstrainableColumns))
import Halo2.Types.EqualityConstraint (EqualityConstraint (EqualityConstraint))
import Halo2.Types.EqualityConstraints (EqualityConstraints (EqualityConstraints))
import Halo2.Types.FixedBound (FixedBound)
import Halo2.Types.FixedValues (FixedValues (FixedValues))
import Halo2.Types.InputExpression (InputExpression (..))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top), LookupTableOutputColumn (LookupTableOutputColumn), Term (Const, IndLess, Lookup, Max, Plus, Times, Var))
import Halo2.Types.LogicConstraints (LogicConstraints (LogicConstraints))
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial (Polynomial))
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (PolynomialConstraints))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.PowerProduct (PowerProduct (PowerProduct, getPowerProduct))
import Halo2.Types.RowCount (RowCount (RowCount))
import Halo2.Types.RowIndex (RowIndex (RowIndex), RowIndexType (Absolute))
import OSL.Map (inverseMap)
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Safe (headMay)
import Stark.Types.Scalar (Scalar, integerToScalar, one, scalarToInteger, toWord64, zero)

class HasPolynomialVariables a where
  getPolynomialVariables :: a -> Set PolynomialVariable

instance HasPolynomialVariables PowerProduct where
  getPolynomialVariables = Map.keysSet . getPowerProduct

instance HasPolynomialVariables PolynomialConstraints where
  getPolynomialVariables cs =
    mconcat $ getPolynomialVariables . snd <$> cs ^. #constraints

instance HasPolynomialVariables Polynomial where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . Map.keys . (^. #monos)

instance HasPolynomialVariables Term where
  getPolynomialVariables =
    \case
      Var x -> Set.singleton x
      Lookup is o ->
        mconcat (rec . (^. #getInputExpression) . fst <$> is)
          <> Set.singleton (PolynomialVariable (o ^. #unLookupTableOutputColumn . #unLookupTableColumn) 0)
      Const _ -> mempty
      Plus x y -> rec x <> rec y
      Times x y -> rec x <> rec y
      Max x y -> rec x <> rec y
      IndLess x y -> rec x <> rec y
    where
      rec = getPolynomialVariables

instance HasPolynomialVariables AtomicLogicConstraint where
  getPolynomialVariables =
    \case
      Equals x y -> getPolynomialVariables x <> getPolynomialVariables y
      LessThan x y -> getPolynomialVariables x <> getPolynomialVariables y

instance HasPolynomialVariables LogicConstraint where
  getPolynomialVariables x =
    case x of
      Atom y -> getPolynomialVariables y
      Not y -> rec y
      And y z -> rec y <> rec z
      Or y z -> rec y <> rec z
      Iff y z -> rec y <> rec z
      Top -> mempty
      Bottom -> mempty
    where
      rec = getPolynomialVariables

instance HasPolynomialVariables LogicConstraints where
  getPolynomialVariables =
    mconcat . fmap (getPolynomialVariables . snd) . (^. #constraints)

deriving newtype instance HasPolynomialVariables a => HasPolynomialVariables (InputExpression a)

instance HasPolynomialVariables a => HasPolynomialVariables (LookupArgument a) where
  getPolynomialVariables x =
    mconcat
      ( getPolynomialVariables (x ^. #gate) :
        (getPolynomialVariables . fst <$> (x ^. #tableMap))
      )

instance HasPolynomialVariables a => HasPolynomialVariables (LookupArguments a) where
  getPolynomialVariables =
    mconcat . fmap getPolynomialVariables . Set.toList . (^. #getLookupArguments)

instance
  (HasPolynomialVariables a, HasPolynomialVariables b) =>
  HasPolynomialVariables (Circuit a b)
  where
  getPolynomialVariables x =
    mconcat
      [ getPolynomialVariables (x ^. #gateConstraints),
        getPolynomialVariables (x ^. #lookupArguments)
      ]

class HasScalars a where
  getScalars :: a -> Set Scalar

instance HasScalars Polynomial where
  getScalars =
    Set.fromList . fmap getCoefficient
      . Map.elems
      . (^. #monos)

instance HasScalars Term where
  getScalars =
    \case
      Var _ -> mempty
      Lookup is _ -> mconcat (getScalars . fst <$> is)
      Const x -> Set.singleton x
      Plus x y -> getScalars x <> getScalars y
      Times x y -> getScalars x <> getScalars y
      Max x y -> getScalars x <> getScalars y
      IndLess x y -> getScalars x <> getScalars y

instance HasScalars AtomicLogicConstraint where
  getScalars =
    \case
      Equals x y -> getScalars x <> getScalars y
      LessThan x y -> getScalars x <> getScalars y

instance HasScalars LogicConstraint where
  getScalars x =
    case x of
      Atom y -> getScalars y
      Not y -> rec y
      And y z -> rec y <> rec z
      Or y z -> rec y <> rec z
      Iff y z -> rec y <> rec z
      Top -> Set.singleton 1
      Bottom -> Set.singleton 0
    where
      rec = getScalars

instance HasScalars LogicConstraints where
  getScalars =
    mconcat . fmap (getScalars . snd) . (^. #constraints)

deriving newtype instance HasScalars a => HasScalars (InputExpression a)

instance HasScalars a => HasScalars (LookupArgument a) where
  getScalars x =
    mconcat
      ( getScalars (x ^. #gate) :
        (getScalars . fst <$> (x ^. #tableMap))
      )

instance HasScalars a => HasScalars (LookupArguments a) where
  getScalars =
    mconcat . fmap getScalars . Set.toList . (^. #getLookupArguments)

instance (HasScalars a, HasScalars b) => HasScalars (Circuit a b) where
  getScalars x =
    mconcat
      [ getScalars (x ^. #gateConstraints),
        getScalars (x ^. #lookupArguments)
      ]

class HasLookupArguments a b where
  getLookupArguments :: a -> LookupArguments b

instance (Ord b, HasLookupArguments a b) => HasLookupArguments [a] b where
  getLookupArguments = mconcat . fmap getLookupArguments

instance HasLookupArguments (InputExpression Term) Term where
  getLookupArguments = getLookupArguments . (^. #getInputExpression)

instance HasLookupArguments Term Term where
  getLookupArguments =
    \case
      Const _ -> mempty
      Var _ -> mempty
      Lookup is (LookupTableOutputColumn o) ->
        LookupArguments
          ( Set.singleton
              (LookupArgument "application" (Const zero) (is <> [(InputExpression (Const zero), o)])) -- good enough for what we need it for, finding the lookup tables
          )
          <> getLookupArguments (fst <$> is)
      Plus x y -> rec x <> rec y
      Times x y -> rec x <> rec y
      Max x y -> rec x <> rec y
      IndLess x y -> rec x <> rec y
    where
      rec = getLookupArguments

instance HasLookupArguments LogicConstraint Term where
  getLookupArguments =
    \case
      Atom (Equals x y) -> term x <> term y
      Atom (LessThan x y) -> term x <> term y
      Not p -> rec p
      And p q -> rec p <> rec q
      Or p q -> rec p <> rec q
      Iff p q -> rec p <> rec q
      Top -> mempty
      Bottom -> mempty
    where
      term = getLookupArguments
      rec = getLookupArguments

instance HasLookupArguments LogicCircuit Term where
  getLookupArguments c =
    (c ^. #lookupArguments)
      <> getLookupArguments (snd <$> (c ^. #gateConstraints . #constraints))

getLookupTables :: HasLookupArguments a b => Ord b => a -> Set (b, [LookupTableColumn])
getLookupTables x =
  Set.fromList
    [ (a ^. #gate, snd <$> (a ^. #tableMap))
      | a <- Set.toList (getLookupArguments x ^. #getLookupArguments)
    ]

class HasColumnVectorToBools a where
  -- Here the a is irrelevant at runtime; it is only passed to select
  -- the correct implementation.
  columnVectorToBools :: a -> Map (RowIndex 'Absolute) (Maybe Scalar) -> Map (RowIndex 'Absolute) Bool

instance HasColumnVectorToBools Polynomial where
  columnVectorToBools _ = fmap (== Just zero)

instance HasColumnVectorToBools Term where
  columnVectorToBools _ = fmap (== Just one)

class HasEvaluate a b | a -> b where
  evaluate :: ann -> Argument -> a -> Either (ErrorMessage ann) b

instance HasEvaluate (RowCount, PolynomialVariable) (Map (RowIndex 'Absolute) Scalar) where
  evaluate _ arg (RowCount n, v) =
    pure . Map.mapKeys ((`mod` n') . subtract (RowIndex $ v ^. #rowIndex . #getRowIndex) . (^. #rowIndex)) $
      Map.filterWithKey
        (\k _ -> (k ^. #colIndex) == v ^. #colIndex)
        (getCellMap arg)
    where
      n' = RowIndex (fromMaybe (die "evaluate PolynomialVariable: row count out of range of Int") (integerToInt (scalarToInteger n)))

instance
  HasEvaluate
    (RowCount, (PowerProduct, Coefficient))
    (Map (RowIndex 'Absolute) Scalar)
  where
  evaluate ann arg (RowCount n, (PowerProduct m, Coefficient c)) =
    if Map.null m
      then do
        n' <- case integerToInt (scalarToInteger n) of
          Just n' -> pure n'
          Nothing -> Left (ErrorMessage ann "row count outside range of Int")
        pure (Map.fromList ((,c) . RowIndex <$> [0 .. n' - 1]))
      else
        fmap (Ring.* c) . foldr (Map.unionWith (Ring.*)) mempty
          <$> sequence
            [ evaluate ann arg (RowCount n, v) <&> fmap (Ring.^ intToInteger (e ^. #getExponent))
              | (v, e) <- Map.toList m
            ]

instance HasEvaluate (RowCount, Polynomial) (Map (RowIndex 'Absolute) (Maybe Scalar)) where
  evaluate ann arg (rc, Polynomial monos) =
    fmap Just . foldr (Map.unionWith (Group.+)) mempty
      <$> mapM (evaluate ann arg . (rc,)) (Map.toList monos)

instance HasEvaluate (RowCount, Term) (Map (RowIndex 'Absolute) (Maybe Scalar)) where
  evaluate ann arg = uncurry $ \rc@(RowCount n) ->
    let rec = evaluate ann arg . (rc,)
     in \case
          Var v -> fmap Just <$> evaluate ann arg (rc, v)
          Const i -> do
            n' <- case integerToInt (scalarToInteger n) of
              Just n' -> pure n'
              Nothing -> Left (ErrorMessage ann "row count outside range of Int")
            pure $ Map.fromList [(RowIndex x, Just i) | x <- [0 .. n' - 1]]
          Plus x y -> Map.unionWith (liftA2 (Group.+)) <$> rec x <*> rec y
          Times x y -> Map.unionWith (liftA2 (Ring.*)) <$> rec x <*> rec y
          Max x y -> Map.unionWith (liftA2 max) <$> rec x <*> rec y
          IndLess x y -> Map.unionWith (liftA2 lessIndicator) <$> rec x <*> rec y
          l@(Lookup is outCol) ->
            mapLeft
              ( \(ErrorMessage ann' msg) ->
                  ErrorMessage ann' ("performLookups " <> pack (show l) <> ": " <> msg)
              )
              (performLookups ann rc arg is outCol)

-- Get the output corresponding to the given input expressions
-- looked up in the given lookup table.
performLookups ::
  HasEvaluate (RowCount, a) (Map (RowIndex 'Absolute) (Maybe Scalar)) =>
  ann ->
  RowCount ->
  Argument ->
  [(InputExpression a, LookupTableColumn)] ->
  LookupTableOutputColumn ->
  Either (ErrorMessage ann) (Map (RowIndex 'Absolute) (Maybe Scalar))
performLookups ann rc arg is outCol = do
  inputTable <-
    fmap (fmap (fromMaybe (die "Halo2.Circuit.performLookups: input expression undefined")))
      <$> mapM (evaluate ann arg . (rc,) . (^. #getInputExpression) . fst) is
  results <-
    getLookupResults
      ann
      rc
      Nothing
      (getCellMap arg)
      (zip inputTable (snd <$> is))
  let allRows = getRowSet rc Nothing
      results' =
        fmap Just . Map.mapKeys (^. #rowIndex) $
          Map.filterWithKey (\k _ -> k ^. #colIndex == outCol') results
  pure $ results' <> Map.fromList ((,Nothing) <$> Set.toList allRows)
  where
    outCol' = outCol ^. #unLookupTableOutputColumn . #unLookupTableColumn

getLookupResults ::
  ann ->
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  Map CellReference Scalar ->
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Either (ErrorMessage ann) (Map CellReference Scalar)
getLookupResults ann rc mRowSet cellMap inputTable = do
  let rowSet = getRowSet rc mRowSet
      allRows = getRowSet rc Nothing
      cellMapAllRows :: Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
      cellMapAllRows = getCellMapRows allRows cellMap
      tableCols :: Map ColumnIndex ()
      tableCols = Map.fromList ((,()) . (^. #unLookupTableColumn) . snd <$> inputTable)
      cellMapTableRows :: Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
      cellMapTableRows = (`Map.intersection` tableCols) <$> cellMapAllRows
      cellMapTableInverse :: Map (Map ColumnIndex Scalar) (RowIndex 'Absolute)
      cellMapTableInverse = inverseMap cellMapTableRows
      tableRows :: Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
      tableRows = getColumnListRows rowSet inputTable
  rowsToCellMap . Map.fromList
    <$> sequence
      [ do
          inputTableRow <-
            maybe
              ( Left
                  ( ErrorMessage
                      ann
                      ("input table row index missing: " <> pack (show (ri, snd <$> inputTable, Map.lookup ri cellMapAllRows)))
                  )
              )
              pure
              (Map.lookup ri tableRows)
          when (Map.size inputTableRow /= length inputTable) $
            Left (ErrorMessage ann ("input table row is wrong size; duplicate column index in lookup table, or missing value in input column vectors? " <> pack (show (snd <$> inputTable, inputTableRow))))
          case Map.lookup inputTableRow cellMapTableInverse of
            Just ri' ->
              case Map.lookup ri' cellMapAllRows of
                Just r -> pure (ri, r)
                Nothing ->
                  Left
                    ( ErrorMessage
                        ann
                        ("argument table row lookup failed: " <> pack (show ri'))
                    )
            Nothing ->
              pure (ri, mempty) -- returning an empty row will result in no cells for this row
        | ri <- Set.toList rowSet
      ]

getRowSet ::
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  Set (RowIndex 'Absolute)
getRowSet (RowCount n) =
  \case
    Nothing ->
      let n' =
            fromMaybe
              (die "getRowSet: row count of range of Int")
              (integerToInt (scalarToInteger n))
       in Set.fromList (RowIndex <$> [0 .. n' - 1])
    Just x -> x

rowsToCellMap ::
  Map (RowIndex 'Absolute) (Map ColumnIndex Scalar) ->
  Map CellReference Scalar
rowsToCellMap rows =
  Map.fromList
    [ (CellReference ci ri, x)
      | (ri, cols) <- Map.toList rows,
        (ci, x) <- Map.toList cols
    ]

-- Gets the row vectors for the given set of rows out of the given cell map.
getCellMapRows ::
  Set (RowIndex 'Absolute) ->
  Map CellReference Scalar ->
  Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
getCellMapRows rows cellMap =
  Map.unionsWith
    (<>)
    [ Map.singleton ri (Map.singleton ci x)
      | (CellReference ci ri, x) <- Map.toList cellMap,
        ri `Set.member` rows
    ]

-- getCellMapColumns ::
--   Map CellReference Scalar ->
--   Map ColumnIndex (Map (RowIndex 'Absolute) Scalar)
-- getCellMapColumns cellMap =
--   Map.unionsWith
--     (<>)
--     [ Map.singleton ci (Map.singleton ri x)
--       | (CellReference ci ri, x) <- Map.toList cellMap
--     ]

columnListToCellMap ::
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Map CellReference Scalar
columnListToCellMap cols =
  Map.fromList
    [ (CellReference ci ri, x)
      | (row, LookupTableColumn ci) <- cols,
        (ri, x) <- Map.toList row
    ]

getColumnListRows ::
  Set (RowIndex 'Absolute) ->
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Map (RowIndex 'Absolute) (Map ColumnIndex Scalar)
getColumnListRows rows = getCellMapRows rows . columnListToCellMap

lessIndicator :: Scalar -> Scalar -> Scalar
lessIndicator x y =
  if x < y then one else zero

instance HasEvaluate (RowCount, AtomicLogicConstraint) (Map (RowIndex 'Absolute) (Maybe Bool)) where
  evaluate ann arg =
    uncurry $ \rc ->
      \case
        Equals x y ->
          Map.intersectionWith (liftA2 (==))
            <$> evaluate ann arg (rc, x)
            <*> evaluate ann arg (rc, y)
        LessThan x y ->
          Map.intersectionWith (liftA2 (<))
            <$> evaluate ann arg (rc, x)
            <*> evaluate ann arg (rc, y)

instance HasEvaluate (RowCount, LogicConstraint) (Map (RowIndex 'Absolute) (Maybe Bool)) where
  evaluate ann arg =
    uncurry $ \rc@(RowCount n) ->
      let getN = case integerToInt (scalarToInteger n) of
            Just n' -> pure n'
            Nothing -> Left (ErrorMessage ann "row count exceeds max Int")
       in \case
            Atom p -> evaluate ann arg (rc, p)
            Not p -> fmap (fmap not) <$> rec (rc, p)
            And p q ->
              Map.intersectionWith (&&^)
                <$> rec (rc, p)
                <*> rec (rc, q)
            Or p q ->
              Map.intersectionWith (||^)
                <$> rec (rc, p)
                <*> rec (rc, q)
            Iff p q ->
              Map.intersectionWith (liftA2 (==))
                <$> rec (rc, p)
                <*> rec (rc, q)
            Top -> do
              n' <- getN
              pure (Map.fromList ((,Just True) . RowIndex <$> [0 .. n' - 1]))
            Bottom -> do
              n' <- getN
              pure (Map.fromList ((,Just False) . RowIndex <$> [0 .. n' - 1]))
    where
      rec = evaluate ann arg

instance HasEvaluate (Map ColumnIndex FixedBound) Bool where
  evaluate _ arg bs =
    pure $
      and
        [ min (toWord64 x) (toWord64 (Group.negate x))
            < b ^. #unFixedBound
          | (ci, b) <- Map.toList bs,
            x <-
              Map.elems
                ( Map.filterWithKey
                    (\k _ -> k ^. #colIndex == ci)
                    (getCellMap arg)
                )
        ]

instance HasEvaluate (RowCount, LogicConstraints) Bool where
  evaluate ann arg (rc, LogicConstraints cs bs) = do
    -- let cols = getCellMapColumns (getCellMap arg)
    (&&) -- trace ("column sizes: " <> show (Map.size <$> cols)) . (&&)
      <$> evaluate ann arg bs
      <*> allM
        ( \(lbl, c) -> do
            r <- evaluate ann arg (rc, c)
            let r' = r == Map.fromList ((,Just True) <$> Set.toList allRows)
            pure r' -- (trace (show (r', lbl, c, Map.filter (== Just False) r)) r')
        )
        cs
    where
      allRows = getRowSet rc Nothing

instance HasEvaluate (RowCount, PolynomialConstraints) Bool where
  evaluate ann arg (rc, PolynomialConstraints polys degreeBound) = do
    allM
      ( \(lbl, poly) ->
          ( degree poly <= degreeBound ^. #getPolynomialDegreeBound
              &&
          )
            . all (== Just zero)
            <$> evaluate ann arg (rc, poly)
      )
      polys

instance
  ( HasColumnVectorToBools a,
    HasEvaluate (RowCount, a) (Map (RowIndex 'Absolute) (Maybe Scalar))
  ) =>
  HasEvaluate (RowCount, LookupArgument a) Bool
  where
  evaluate ann arg (rc, LookupArgument lbl gate tableMap) = do
    gateVals <- columnVectorToBools gate <$> evaluate ann arg (rc, gate)
    let rowSet = Map.keysSet (Map.filter id gateVals)
    inputTable <-
      fmap (fmap (fromMaybe (die "Halo2.Circuit.evaluate @LookupArgument: input expression undefined")))
        <$> mapM (evaluate ann arg . (rc,) . (^. #getInputExpression) . fst) tableMap
    results <-
      getLookupResults
        ann
        rc
        (Just rowSet)
        (getCellMap arg)
        (zip inputTable (snd <$> tableMap))
    let rowSet' =
          Set.fromList . fmap (^. #rowIndex) . Map.keys $
            results
    pure $ rowSet' == rowSet

instance
  HasEvaluate (RowCount, LookupArgument a) Bool =>
  HasEvaluate (RowCount, LookupArguments a) Bool
  where
  evaluate ann arg =
    uncurry $ \rc -> allM (evaluate ann arg . (rc,)) . Set.toList . (^. #getLookupArguments)

instance
  (HasEvaluate (RowCount, a) Bool, HasEvaluate (RowCount, LookupArguments b) Bool) =>
  HasEvaluate (Circuit a b) Bool
  where
  evaluate ann arg c =
    and
      <$> sequence
        [ evaluate ann arg (c ^. #columnTypes),
          evaluate ann arg (c ^. #rowCount),
          evaluate ann arg (c ^. #rowCount, c ^. #gateConstraints),
          evaluate ann arg (c ^. #rowCount, c ^. #lookupArguments),
          evaluate
            ann
            arg
            ( c ^. #equalityConstrainableColumns,
              c ^. #equalityConstraints
            ),
          evaluate ann arg (c ^. #fixedValues)
        ]

instance HasEvaluate ColumnTypes Bool where
  evaluate _ arg (ColumnTypes m) =
    pure $
      getColumns (arg ^. #statement . #unStatement)
        == Map.keysSet (Map.filter (== Instance) m)
        && getColumns (arg ^. #witness . #unWitness)
          == Map.keysSet (Map.filter (== Advice) m)
            `Set.union` Map.keysSet (Map.filter (== Fixed) m)

instance HasEvaluate (FixedValues (RowIndex Absolute)) Bool where
  evaluate _ arg fvs =
    pure $
      fixedValuesToCellMap fvs `Map.isSubmapOf` (arg ^. #witness . #unWitness)

fixedValuesToCellMap :: FixedValues (RowIndex 'Absolute) -> Map CellReference Scalar
fixedValuesToCellMap (FixedValues m) =
  Map.fromList
    [ (CellReference colIdx rowIdx, v)
      | (colIdx, col) <- Map.toList m,
        (rowIdx, v) <- Map.toList (col ^. #unFixedColumn)
    ]

instance HasEvaluate (EqualityConstrainableColumns, EqualityConstraints) Bool where
  evaluate _ _ (eqcs, eqs) =
    pure $ equalityConstraintsMatchEqualityConstrainableColumns eqcs eqs

equalityConstraintsMatchEqualityConstrainableColumns ::
  EqualityConstrainableColumns ->
  EqualityConstraints ->
  Bool
equalityConstraintsMatchEqualityConstrainableColumns
  (EqualityConstrainableColumns eqcs)
  (EqualityConstraints eqs) =
    all f eqs
    where
      f (EqualityConstraint cells) =
        Set.map (^. #colIndex) cells `Set.isSubsetOf` eqcs

instance HasEvaluate RowCount Bool where
  evaluate _ arg (RowCount n) =
    pure $
      f (arg ^. #statement . #unStatement)
        && f (arg ^. #witness . #unWitness)
    where
      f m =
        let cols = getColumns m
         in and
              [ Set.fromList (RowIndex <$> [0 .. n' - 1])
                  == Map.keysSet (getColumn i m)
                | i <- Set.toList cols
              ]

      n' =
        fromMaybe (die "Halo2.Circuit.evaluate: row count out of range of Int") $
          integerToInt (scalarToInteger n)

getColumns :: Map CellReference Scalar -> Set ColumnIndex
getColumns =
  Set.map (^. #colIndex) . Map.keysSet

getColumn :: ColumnIndex -> Map CellReference Scalar -> Map (RowIndex 'Absolute) Scalar
getColumn colIndex =
  Map.mapKeys (^. #rowIndex) . Map.filterWithKey (\k _ -> k ^. #colIndex == colIndex)

getCellMap :: Argument -> Map CellReference Scalar
getCellMap arg = (arg ^. #statement . #unStatement) `Map.union` (arg ^. #witness . #unWitness)
