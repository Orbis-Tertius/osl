{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Trace.Semantics
  ( evalTrace
  ) where

import qualified Algebra.Additive as Group
import qualified Algebra.Ring as Ring
import Cast (integerToInt)
import Control.Lens ((^.), (<&>))
import Control.Monad (forM_, forM, when, unless, void)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (maybeToList)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (pack)
-- import Debug.Trace (trace)
import Halo2.Types.Coefficient (Coefficient)
import Halo2.Types.CellReference (CellReference (CellReference))
import Halo2.Types.ColumnIndex (ColumnIndex)
import Halo2.Types.FixedValues (FixedValues)
import Halo2.Types.InputExpression (InputExpression)
import Halo2.Types.LookupArguments (LookupArguments)
import Halo2.Types.LookupArgument (LookupArgument)
import Halo2.Types.LookupTableColumn (LookupTableColumn)
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints)
import Halo2.Types.PowerProduct (PowerProduct)
import Halo2.Types.RowIndex (RowIndex (RowIndex))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import Stark.Types.Scalar (Scalar, scalarToInteger, zero, one, integerToScalar)
import Trace.Types (TraceType, Trace, Case (Case), SubexpressionId, ResultExpressionId (ResultExpressionId), SubexpressionTrace, StepType)
import Trace.Types.EvaluationContext (EvaluationContext (EvaluationContext), ContextType (Global, Local))

evalTrace ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
evalTrace ann tt t = do
  checkAllResultsArePresentForUsedCases ann tt t
  checkAllStepConstraintsAreSatisfied ann tt t
  checkAllEqualityConstraintsAreSatisfied ann tt t

checkAllResultsArePresentForUsedCases ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
checkAllResultsArePresentForUsedCases ann tt t =
  forM_ (t ^. #usedCases) $ \c ->
    forM_ (tt ^. #results) $ \(ResultExpressionId sId) ->
      maybe
        (Left
          (ErrorMessage ann
            ("result is not present: "
              <> pack (show (c, sId)))))
        (const (pure ()))
        (Map.lookup (c, sId) (t ^. #subexpressions))

checkAllStepConstraintsAreSatisfied ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
checkAllStepConstraintsAreSatisfied ann tt t = do
  gc <- getGlobalEvaluationContext ann tt t
  forM_ (Map.toList (t ^. #subexpressions)) $ \((c, sId), sT) -> do
    lc <- getSubexpressionEvaluationContext ann tt t gc (c, sId, sT)
    checkStepConstraintsAreSatisfied ann tt sT lc

checkStepConstraintsAreSatisfied ::
  ann ->
  TraceType ->
  SubexpressionTrace ->
  EvaluationContext 'Local ->
  Either (ErrorMessage ann) ()
checkStepConstraintsAreSatisfied ann tt sT ec =
  case Map.lookup (sT ^. #stepType) (tt ^. #stepTypes) of
    Just st -> do
      checkPolynomialConstraints ann ec (st ^. #gateConstraints)
      checkLookupArguments ann ec (st ^. #lookupArguments)
    Nothing -> Left (ErrorMessage ann "step type id not defined in trace type")

checkPolynomialConstraints ::
  ann ->
  EvaluationContext 'Local ->
  PolynomialConstraints ->
  Either (ErrorMessage ann) ()
checkPolynomialConstraints ann ec cs =
  void $ sequence
    [ do z <- evalPolynomial ann ec c
         unless (z == zero) (Left (ErrorMessage ann "polynomial constraint not satisfied"))
      | c <- cs ^. #constraints
    ]

evalPolynomial ::
  ann ->
  EvaluationContext 'Local ->
  Polynomial ->
  Either (ErrorMessage ann) Scalar
evalPolynomial ann ec p =
  foldr (Group.+) zero <$>
    mapM (evalMonomial ann ec) (Map.toList (p ^. #monos))

evalMonomial ::
  ann ->
  EvaluationContext 'Local ->
  (PowerProduct, Coefficient) ->
  Either (ErrorMessage ann) Scalar
evalMonomial ann ec (pp, c) =
  (Ring.* (c ^. #getCoefficient)) <$> evalPowerProduct ann ec pp

evalPowerProduct ::
  ann ->
  EvaluationContext 'Local ->
  PowerProduct ->
  Either (ErrorMessage ann) Scalar
evalPowerProduct ann ec pp =
  foldr (Ring.*) one <$>
    mapM (\(v, e) -> (^ e) <$> evalPolynomialVariable ann ec v)
      (Map.toList (pp ^. #getPowerProduct))

evalPolynomialVariable ::
  ann ->
  EvaluationContext 'Local ->
  PolynomialVariable ->
  Either (ErrorMessage ann) Scalar
evalPolynomialVariable ann ec v =
  case v ^. #rowIndex of
    0 ->
      maybe
        (Left (ErrorMessage ann "variable not defined in local mappings"))
        pure
        (Map.lookup (v ^. #colIndex) (ec ^. #localMappings))
    _ ->
      Left (ErrorMessage ann "unsupported: nonzero relative row index in polynomial variable in step constraint")

checkLookupArguments ::
  ann ->
  EvaluationContext 'Local ->
  LookupArguments Polynomial ->
  Either (ErrorMessage ann) ()
checkLookupArguments ann ec args =
  mapM_ (checkLookupArgument ann ec) (args ^. #getLookupArguments)

checkLookupArgument ::
  ann ->
  EvaluationContext 'Local ->
  LookupArgument Polynomial ->
  Either (ErrorMessage ann) ()
checkLookupArgument ann ec arg = do
  g <- evalPolynomial ann ec (arg ^. #gate)
  when (g == zero) $ do
    is <- evalInputExpressions ann ec (arg ^. #tableMap)
    case Map.lookup (Set.fromList (snd <$> arg ^. #tableMap))
           (ec ^. #lookupTables) of
      Just t ->
        unless (is `Set.member` t)
          (Left (ErrorMessage ann "lookup argument is not satisfied"))
      Nothing ->
        Left (ErrorMessage ann "lookup table is not cached in the context")

evalInputExpressions ::
  ann ->
  EvaluationContext 'Local ->
  [(InputExpression Polynomial, LookupTableColumn)] ->
  Either (ErrorMessage ann) (Map LookupTableColumn Scalar)
evalInputExpressions ann ec is =
  Map.fromList <$> sequence
    [ (col,) <$> evalPolynomial ann ec (e ^. #getInputExpression)
      | (e, col) <- is
    ]

checkAllEqualityConstraintsAreSatisfied ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) ()
checkAllEqualityConstraintsAreSatisfied ann tt t = do
  cellMap <- getGlobalCellMap <$> getGlobalEvaluationContext ann tt t
  forM_ (tt ^. #equalityConstraints . #getEqualityConstraints) $ \eq -> do
    vs <- mapM (lookupCellReference ann cellMap) (Set.toList (eq ^. #getEqualityConstraint))
    case vs of
      [] -> pure ()
      (v:_) -> when (not (all (== v) vs)) (Left (ErrorMessage ann "equality constraint not satisifed"))

lookupCellReference ::
  ann ->
  Map CellReference Scalar ->
  CellReference ->
  Either (ErrorMessage ann) Scalar
lookupCellReference ann m r =
  maybe (Left (ErrorMessage ann "cell reference lookup failed"))
    pure (Map.lookup r m)

getGlobalCellMap ::
  EvaluationContext t ->
  Map CellReference Scalar
getGlobalCellMap ec =
  Map.fromList
    [ (CellReference ci ri, x)
      | ((c, ci), x) <- Map.toList (ec ^. #globalMappings),
        ri <- maybeToList $ RowIndex <$> integerToInt (scalarToInteger (c ^. #unCase))
    ]

addFixedValuesToEvaluationContext ::
  EvaluationContext 'Global ->
  FixedValues ->
  EvaluationContext 'Global
addFixedValuesToEvaluationContext ec vs =
  ec' <> ec
  where
    ec' =
      EvaluationContext
        (Map.fromList
          [ ((Case i', col), x)
            | (col, vs') <- Map.toList (vs ^. #getFixedValues),
              (i, x) <- zip [0..] (vs' ^. #unFixedColumn),
              i' <- maybeToList (integerToScalar i)
          ]
        )
        mempty
        mempty

getGlobalEvaluationContext ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) (EvaluationContext 'Global)
getGlobalEvaluationContext ann tt t = do
  let gms = getGlobalMappings tt t
      ec = foldl' addFixedValuesToEvaluationContext
           (EvaluationContext gms mempty mempty)
           (Map.elems (tt ^. #stepTypes) <&> (^. #fixedValues))
  EvaluationContext gms mempty
    <$> (Map.fromList <$> sequence
          [ (cs,) <$> getLookupTable ann tt t ec cs
            | cs <- Set.toList (traceTypeLookupTables tt)
          ])

getGlobalMappings ::
  TraceType ->
  Trace ->
  Map (Case, ColumnIndex) Scalar
getGlobalMappings tt t =
  mconcat
    [ t ^. #statement . #unStatement,
      t ^. #witness . #unWitness,
      getCaseNumberColumnMappings tt t
    ]

getCaseNumberColumnMappings ::
  TraceType ->
  Trace ->
  Map (Case, ColumnIndex) Scalar
getCaseNumberColumnMappings tt t =
  Map.fromList
    [ ((i, col), i ^. #unCase) | i <- Set.toList (t ^. #usedCases) ]
  where
    col = tt ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex

traceTypeLookupTables ::
  TraceType ->
  Set (Set LookupTableColumn)
traceTypeLookupTables tt =
  mconcat (stepTypeLookupTables <$> Map.elems (tt ^. #stepTypes))

stepTypeLookupTables ::
  StepType ->
  Set (Set LookupTableColumn)
stepTypeLookupTables st =
  Set.map lookupArgumentTable (st ^. #lookupArguments . #getLookupArguments)

lookupArgumentTable ::
  LookupArgument Polynomial ->
  Set LookupTableColumn
lookupArgumentTable arg =
  Set.fromList ((arg ^. #tableMap) <&> snd)

getSubexpressionEvaluationContext ::
  ann ->
  TraceType ->
  Trace ->
  EvaluationContext 'Global ->
  (Case, SubexpressionId, SubexpressionTrace) ->
  Either (ErrorMessage ann) (EvaluationContext 'Local)
getSubexpressionEvaluationContext ann tt t gc (c, sId, sT) =
    EvaluationContext
      (gc ^. #globalMappings)
      <$> localMappings
      <*> pure (gc ^. #lookupTables)
  where
    localMappings =
      mconcat <$> sequence
        [ inputMappings,
          outputMapping,
          caseNumberMapping,
          stepTypeMapping,
          stepIndicatorMapping,
          globalToLocalMappings,
          pure (sT ^. #adviceValues)
        ]

    inputMappings =
      case Set.toList
             (Set.filter
               (\l -> l ^. #stepType == sT ^. #stepType
                  && l ^. #output . #unOutputSubexpressionId == sId)
               (tt ^. #links)) of
        [l] ->
          mconcat <$> sequence
            [ case Map.lookup (c, iId) (t ^. #subexpressions) of
                Just sT' -> pure (Map.singleton col (sT' ^. #value))
                Nothing ->
                  -- trace (show (t ^. #subexpressions)) $
                  Left (ErrorMessage ann ("expected input not present: " <> pack (show (c, iId, l ^. #inputs, sT))))
              | (col, iId) <- zip ((tt ^. #inputColumnIndices) <&> (^. #unInputColumnIndex))
                                  ((l ^. #inputs) <&> (^. #unInputSubexpressionId))
            ]
        [] -> Left (ErrorMessage ann "no links found for this subexpression's step type and id")
        _ -> Left (ErrorMessage ann "more than one link found for this subexpression's step type and id; this is a malformed links set")

    outputMapping =
      pure $ Map.singleton (tt ^. #outputColumnIndex . #unOutputColumnIndex) (sT ^. #value)

    caseNumberMapping =
      pure (Map.singleton (tt ^. #caseNumberColumnIndex . #unCaseNumberColumnIndex) (c ^. #unCase))

    stepTypeMapping =
      pure (Map.singleton (tt ^. #stepTypeColumnIndex . #unStepTypeColumnIndex) (sT ^. #stepType . #unStepTypeId))

    stepIndicatorMapping =
      pure (Map.singleton (tt ^. #stepIndicatorColumnIndex . #unStepIndicatorColumnIndex) zero)

    globalToLocalMappings =
      pure $ Map.mapKeys snd (Map.filterWithKey (\(c',_) _ -> c' == c) (gc ^. #globalMappings))

getLookupTable ::
  ann ->
  TraceType ->
  Trace ->
  EvaluationContext 'Global ->
  Set LookupTableColumn ->
  Either (ErrorMessage ann) (Set (Map LookupTableColumn Scalar))
getLookupTable ann tt t gc cs =
  fmap Set.fromList $ forM (Map.toList (t ^. #subexpressions)) $ \((c, sId), sT) -> do
    lc <- getSubexpressionEvaluationContext ann tt t gc (c, sId, sT)
    Map.fromList <$> sequence
      [ maybe (Left (ErrorMessage ann "lookup table has a hole"))
          (pure . (col,)) (Map.lookup (col ^. #unLookupTableColumn) (lc ^. #localMappings))
       | col <- Set.toList cs
      ]
