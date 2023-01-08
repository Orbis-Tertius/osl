{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Halo2.Circuit
  ( HasPolynomialVariables (getPolynomialVariables),
    HasScalars (getScalars),
    HasLookupArguments (getLookupArguments),
    getLookupTables,
    HasEvaluate (evaluate),
  )
where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (integerToInt, intToInteger)
import Control.Lens ((<&>))
import Control.Monad.Extra (allM)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Die (die)
import Halo2.Polynomial (degree)
import Halo2.Prelude
import Halo2.Types.Argument (Argument)
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.Circuit (Circuit, LogicCircuit)
import Halo2.Types.Coefficient (Coefficient (Coefficient, getCoefficient))
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.ColumnType (ColumnType (Fixed, Advice, Instance))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.EqualityConstrainableColumns (EqualityConstrainableColumns (EqualityConstrainableColumns))
import Halo2.Types.EqualityConstraint (EqualityConstraint (EqualityConstraint))
import Halo2.Types.EqualityConstraints (EqualityConstraints (EqualityConstraints))
import Halo2.Types.FixedValues (FixedValues (FixedValues))
import Halo2.Types.InputExpression (InputExpression (..))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (Equals, LessThan), LogicConstraint (And, Atom, Bottom, Iff, Not, Or, Top), LookupTableOutputColumn (LookupTableOutputColumn), Term (Const, IndLess, Lookup, Max, Plus, Times, Var))
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import Halo2.Types.Polynomial (Polynomial (Polynomial))
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (PolynomialConstraints))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.PowerProduct (PowerProduct (PowerProduct, getPowerProduct))
import Halo2.Types.RowCount (RowCount (RowCount))
import Halo2.Types.RowIndex (RowIndex (RowIndex), RowIndexType (Absolute))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Stark.Types.Scalar (Scalar, zero, one, scalarToInteger)

class HasPolynomialVariables a where
  getPolynomialVariables :: a -> Set PolynomialVariable

instance HasPolynomialVariables PowerProduct where
  getPolynomialVariables = Map.keysSet . getPowerProduct

instance HasPolynomialVariables PolynomialConstraints where
  getPolynomialVariables cs =
    mconcat $ getPolynomialVariables <$> cs ^. #constraints

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
    mconcat . fmap getPolynomialVariables . (^. #constraints)

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
    mconcat . fmap getScalars . (^. #constraints)

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
    (c ^. #lookupArguments) <> getLookupArguments (c ^. #gateConstraints . #constraints)

getLookupTables :: HasLookupArguments a b => Ord b => a -> Set (b, [LookupTableColumn])
getLookupTables x =
  Set.fromList
    [ (a ^. #gate, snd <$> (a ^. #tableMap))
      | a <- Set.toList (getLookupArguments x ^. #getLookupArguments)
    ]

class HasEvaluate a b | a -> b where
  evaluate :: ann -> Argument -> a -> Either (ErrorMessage ann) b

instance HasEvaluate PolynomialVariable (Map (RowIndex 'Absolute) Scalar) where
  evaluate _ arg v =
    pure . Map.mapKeys (^. #rowIndex) $
      Map.filterWithKey
        (\k _ -> (k ^. #colIndex) == v ^. #colIndex)
        (getCellMap arg)

instance HasEvaluate (PowerProduct, Coefficient) (Map (RowIndex 'Absolute) Scalar) where
  evaluate ann arg (PowerProduct m, Coefficient c) =
    fmap (Ring.* c) . foldr (Map.unionWith (Ring.*)) mempty <$> sequence
      [ evaluate ann arg v <&> fmap (Ring.^ intToInteger (e ^. #getExponent))
       | (v, e) <- Map.toList m ]

instance HasEvaluate Polynomial (Map (RowIndex 'Absolute) Scalar) where
  evaluate ann arg (Polynomial monos) =
    foldr (Map.unionWith (Group.+)) mempty
      <$> mapM (evaluate ann arg) (Map.toList monos)

instance HasEvaluate (RowCount, Term) (Map (RowIndex 'Absolute) Scalar) where
  evaluate ann arg = uncurry $ \rc@(RowCount n) ->
    let rec = evaluate ann arg . (rc,) in
    \case
      Var v -> evaluate ann arg v
      Const i -> do
        n' <- case integerToInt (scalarToInteger n) of
                Just n' -> pure n'
                Nothing -> Left (ErrorMessage ann "row count outside range of Int")
        pure $ Map.fromList [(RowIndex x, i) | x <- [0..n'-1]]
      Plus x y -> Map.unionWith (Group.+) <$> rec x <*> rec y
      Times x y -> Map.unionWith (Ring.*) <$> rec x <*> rec y
      Max x y -> Map.unionWith max <$> rec x <*> rec y
      IndLess x y -> Map.intersectionWith lessIndicator <$> rec x <*> rec y
      Lookup is outCol -> performLookups ann rc Nothing arg is outCol

-- Get the column vector of outputs corresponding to the given input expressions
-- looked up in the given lookup table. The lookups are performed only on the given
-- set of rows indices. If no set of row indices is provided, then the lookup is
-- performed on all rows.
performLookups ::
  ann ->
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  Argument ->
  [(InputExpression Term, LookupTableColumn)] ->
  LookupTableOutputColumn ->
  Either (ErrorMessage ann) (Map (RowIndex 'Absolute) Scalar)
performLookups ann rc mRowSet arg is outCol = do
  inputTable <- mapM (evaluate ann arg . (rc,) . (^. #getInputExpression) . fst) is
  permutation <- getLookupResults ann rc mRowSet (getCellMap arg) (zip inputTable (snd <$> is))
  pure . Map.fromList $
    [ (cell ^. #rowIndex, v)
     | (cell, v) <- Map.toList permutation,
       cell ^. #colIndex == outCol ^. #unLookupTableOutputColumn . #unLookupTableColumn
    ]

-- Succeeds only if each lookup table input row expressed by the provided
-- column vectors is a member of the lookup table as expressed by the cell map, and
-- the rows so expressed cover the provided set of row indices, or all rows if
-- there is no provided set of row indices. Returns a cell map resulting from
-- rearranging the rows (with duplications and deletions allowed) of the provided
-- cell map, such that the lookup argument input table is expressed in that
-- cell map.
getLookupResults ::
  ann ->
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  Map CellReference Scalar ->
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Either (ErrorMessage ann) (Map CellReference Scalar)
getLookupResults ann rc mRowSet cellMap table = do
  cellMapRows <- getCellMapRows ann rc mRowSet cellMap
  tableRows <- getColumnListRows ann rc mRowSet table
  todo cellMapRows tableRows

getCellMapRows ::
  ann ->
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  Map CellReference Scalar ->
  Either (ErrorMessage ann) (Map (RowIndex 'Absolute) (Map ColumnIndex Scalar))
getCellMapRows = todo

getColumnListRows ::
  ann ->
  RowCount ->
  Maybe (Set (RowIndex 'Absolute)) ->
  [(Map (RowIndex 'Absolute) Scalar, LookupTableColumn)] ->
  Either (ErrorMessage ann) (Map (RowIndex 'Absolute) (Map ColumnIndex Scalar))
getColumnListRows = todo

lessIndicator :: Scalar -> Scalar -> Scalar
lessIndicator x y =
  if x < y then one else zero

instance HasEvaluate AtomicLogicConstraint Bool where
  evaluate = todo

instance HasEvaluate LogicConstraint Bool where
  evaluate = todo

instance HasEvaluate LogicConstraints Bool where
  evaluate = todo

instance HasEvaluate PolynomialConstraints Bool where
  evaluate ann arg (PolynomialConstraints polys degreeBound) = do
    allM (\poly -> (degree poly <= degreeBound ^. #getPolynomialDegreeBound
               &&) . all (== 0) <$> evaluate ann arg poly)
        polys

instance HasEvaluate (LookupArguments Polynomial) Bool where
  evaluate = todo

instance HasEvaluate (LookupArguments Term) Bool where
  evaluate = todo

instance ( HasEvaluate a Bool, HasEvaluate (LookupArguments b) Bool ) =>
         HasEvaluate (Circuit a b) Bool where
  evaluate ann arg c =
    and <$> sequence
      [ evaluate ann arg (c ^. #columnTypes),
        evaluate ann arg (c ^. #rowCount),
        evaluate ann arg (c ^. #gateConstraints),
        evaluate ann arg (c ^. #lookupArguments),
        evaluate ann arg (c ^. #equalityConstrainableColumns,
                          c ^. #equalityConstraints),
        evaluate ann arg (c ^. #fixedValues)
      ]

instance HasEvaluate ColumnTypes Bool where
  evaluate _ arg (ColumnTypes m) =
    pure $ getColumns (arg ^. #statement . #unStatement) ==
      Map.keysSet (Map.filter (== Instance) m) &&
      getColumns (arg ^. #witness . #unWitness) ==
      (Map.keysSet (Map.filter (== Advice) m) `Set.union`
         Map.keysSet (Map.filter (== Fixed) m))

instance HasEvaluate FixedValues Bool where
  evaluate _ arg fvs = pure $
    fixedValuesToCellMap fvs `Map.isSubmapOf` (arg ^. #witness . #unWitness)

fixedValuesToCellMap :: FixedValues -> Map CellReference Scalar
fixedValuesToCellMap (FixedValues m) =
  Map.fromList
    [ (CellReference colIdx rowIdx, v)
     | (colIdx, col) <- Map.toList m,
       (rowIdx, v) <- zip (RowIndex <$> [0..]) (col ^. #unFixedColumn)
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
     pure $ f (arg ^. #statement . #unStatement)
         && f (arg ^. #witness . #unWitness)
    where
      f m =
        let cols = getColumns m
        in and [ Set.fromList (RowIndex <$> [0 .. n' - 1])
                   == Map.keysSet (getColumn i m)
                | i <- Set.toList cols
               ]

      n' = fromMaybe (die "Halo2.Circuit.evaluate: row count out of range of Int")
             $ integerToInt (scalarToInteger n)

getColumns :: Map CellReference Scalar -> Set ColumnIndex
getColumns =
  Set.map (^. #colIndex) . Map.keysSet

getColumn :: ColumnIndex -> Map CellReference Scalar -> Map (RowIndex 'Absolute) Scalar
getColumn colIndex =
  Map.mapKeys (^. #rowIndex) . Map.filterWithKey (\k _ -> k ^. #colIndex == colIndex)

getCellMap :: Argument -> Map CellReference Scalar
getCellMap arg = (arg ^. #statement . #unStatement) `Map.union` (arg ^. #witness . #unWitness)

todo :: a
todo = todo
