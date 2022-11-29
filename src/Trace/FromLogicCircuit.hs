{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}

module Trace.FromLogicCircuit
  ( logicCircuitToTraceType,
    getMapping,
  )
where

import Cast (intToInteger)
import Control.Applicative ((<|>))
import Control.Lens ((<&>))
import Control.Monad (foldM, mzero, replicateM)
import Control.Monad.Trans.State (State, evalState, get, put)
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Die (die)
import Halo2.ByteDecomposition (countBytes)
import Halo2.Circuit (getLookupTables, getPolynomialVariables, getScalars)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import Halo2.Types.BitsPerByte (BitsPerByte)
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.Coefficient (Coefficient)
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Advice))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.Exponent (Exponent)
import Halo2.Types.FixedColumn (FixedColumn (FixedColumn))
import Halo2.Types.FixedValues (FixedValues (FixedValues))
import Halo2.Types.InputExpression (InputExpression (InputExpression))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint, LogicConstraint)
import qualified Halo2.Types.LogicConstraint as LC
import Halo2.Types.LogicConstraints (LogicConstraints)
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (..))
import Halo2.Types.PolynomialDegreeBound (PolynomialDegreeBound (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Halo2.Types.PowerProduct (PowerProduct)
import Halo2.Types.RowCount (RowCount (RowCount))
import OSL.Types.Arity (Arity (Arity))
import Stark.Types.Scalar (Scalar, integerToScalar)
import Trace.Types (CaseNumberColumnIndex (..), InputColumnIndex (..), NumberOfCases (NumberOfCases), OutputColumnIndex (..), ResultExpressionId (ResultExpressionId), StepIndicatorColumnIndex (..), StepType (StepType), StepTypeColumnIndex (..), StepTypeId (StepTypeId), SubexpressionId (SubexpressionId), SubexpressionLink, TraceType (TraceType))

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
    (getResultExpressionId mapping)
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

    stepTypes = getStepTypes c mapping

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
  | TimesAnd -- and & are the same operation, actually
  | Or
  | Not
  | Iff
  | Equals
  | LessThan
  | VoidT

type StepTypeIdOf :: Operator -> Type
newtype StepTypeIdOf a = StepTypeIdOf {unOf :: StepTypeId}
  deriving (Generic)

data StepTypeIdMapping = StepTypeIdMapping
  { loads :: Map PolynomialVariable StepTypeId,
    lookups :: Map [LookupTableColumn] StepTypeId,
    constants :: Map Scalar StepTypeId,
    plus :: StepTypeIdOf Plus,
    timesAnd :: StepTypeIdOf TimesAnd,
    or :: StepTypeIdOf Or,
    not :: StepTypeIdOf Not,
    iff :: StepTypeIdOf Iff,
    equals :: StepTypeIdOf Equals,
    lessThan :: StepTypeIdOf LessThan,
    voidT :: StepTypeIdOf VoidT
  }
  deriving (Generic)

type SubexpressionIdOf :: Type -> Type
newtype SubexpressionIdOf a = SubexpressionIdOf {unOf :: SubexpressionId}
  deriving (Generic)

type Void :: Type
data Void

data Operation
  = Or' SubexpressionId SubexpressionId
  | Not' SubexpressionId
  | Iff' SubexpressionId SubexpressionId
  | Plus' SubexpressionId SubexpressionId
  | TimesAnd' SubexpressionId SubexpressionId
  | Equals' SubexpressionId SubexpressionId
  | LessThan' SubexpressionId SubexpressionId
  deriving (Eq, Ord)

data SubexpressionIdMapping = SubexpressionIdMapping
  { void :: Maybe (SubexpressionIdOf Void),
    result :: Maybe ResultExpressionId,
    variables :: Map PolynomialVariable (SubexpressionIdOf PolynomialVariable),
    lookups :: Map LookupArgument (SubexpressionIdOf LookupArgument),
    constants :: Map Scalar (SubexpressionIdOf Scalar),
    operations :: Map Operation (SubexpressionIdOf Operation)
  }
  deriving (Generic)

instance Semigroup SubexpressionIdMapping where
  (SubexpressionIdMapping a b c d e f) <> (SubexpressionIdMapping g h i j k l) =
    SubexpressionIdMapping (a <|> g) (b <|> h) (c <> i) (d <> j) (e <> k) (f <> l)

getStepArity :: LogicCircuit -> Arity
getStepArity = max 2 . getLookupArgumentsArity . (^. #lookupArguments)

getLookupArgumentsArity :: LookupArguments -> Arity
getLookupArgumentsArity =
  foldl' max 0 . fmap (Arity . length . (^. #tableMap))
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
        (StepTypeId 0)
        (SubexpressionId 0)

    nextCol :: State S ColumnIndex
    nextCol = do
      S i j k <- get
      put (S (i + 1) j k)
      pure i

    nextSid :: State S StepTypeId
    nextSid = do
      S i j k <- get
      put (S i (j + 1) k)
      pure j

    nextSid' :: State S (StepTypeIdOf a)
    nextSid' = StepTypeIdOf <$> nextSid

    nextEid :: State S SubexpressionId
    nextEid = do
      S i j k <- get
      put (S i j (k + 1))
      pure k

    nextEid' :: State S (SubexpressionIdOf a)
    nextEid' = SubexpressionIdOf <$> nextEid

    go :: State S Mapping
    go =
      Mapping
        <$> (CaseNumberColumnIndex <$> nextCol)
        <*> (StepTypeColumnIndex <$> nextCol)
        <*> (StepIndicatorColumnIndex <$> nextCol)
        <*> replicateM
          (getStepArity c ^. #unArity)
          (InputColumnIndex <$> nextCol)
        <*> (OutputColumnIndex <$> nextCol)
        <*> ( ByteDecompositionMapping bitsPerByte
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
        <*> ( StepTypeIdMapping
                <$> ( Map.fromList . zip polyVars
                        <$> replicateM (length polyVars) nextSid
                    )
                <*> ( Map.fromList . zip lookupTables
                        <$> replicateM (length lookupTables) nextSid
                    )
                <*> ( Map.fromList . zip scalars
                        <$> replicateM (length scalars) nextSid
                    )
                <*> (nextSid' :: State S (StepTypeIdOf Plus))
                <*> (nextSid' :: State S (StepTypeIdOf TimesAnd))
                <*> (nextSid' :: State S (StepTypeIdOf Or))
                <*> (nextSid' :: State S (StepTypeIdOf Not))
                <*> (nextSid' :: State S (StepTypeIdOf Iff))
                <*> (nextSid' :: State S (StepTypeIdOf Equals))
                <*> (nextSid' :: State S (StepTypeIdOf LessThan))
                <*> (nextSid' :: State S (StepTypeIdOf VoidT))
            )
        <*> ( do
                m0 <-
                  SubexpressionIdMapping
                    <$> (Just <$> (nextEid' :: State S (SubexpressionIdOf Void)))
                    <*> (Just . ResultExpressionId <$> nextEid)
                    <*> ( Map.fromList . zip polyVars
                            <$> replicateM (length polyVars) nextEid'
                        )
                    <*> ( Map.fromList . zip lookupArguments
                            <$> replicateM (length lookupArguments) nextEid'
                        )
                    <*> ( Map.fromList . zip scalars
                            <$> replicateM (length scalars) nextEid'
                        )
                    <*> pure mempty
                traverseConstraints m0 (c ^. #gateConstraints)
            )

    traverseConstraints :: SubexpressionIdMapping -> LogicConstraints -> State S SubexpressionIdMapping
    traverseConstraints m' lcs =
      foldM (\x y -> snd <$> traverseConstraint x y) m' (lcs ^. #constraints)

    traverseConstraint :: SubexpressionIdMapping -> LogicConstraint -> State S (SubexpressionId, SubexpressionIdMapping)
    traverseConstraint m' =
      \case
        LC.Atom x -> traverseAtom m' x
        LC.Not x -> do
          (xId, m'') <- traverseConstraint m' x
          addOp m'' (Not' xId) <$> nextEid'
        LC.And x y -> do
          (xId, m'') <- traverseConstraint m' x
          (yId, m''') <- traverseConstraint m'' y
          addOp m''' (TimesAnd' xId yId) <$> nextEid'
        LC.Or x y -> do
          (xId, m'') <- traverseConstraint m' x
          (yId, m''') <- traverseConstraint m'' y
          addOp m''' (Or' xId yId) <$> nextEid'
        LC.Iff x y -> do
          (xId, m'') <- traverseConstraint m' x
          (yId, m''') <- traverseConstraint m'' y
          addOp m''' (Iff' xId yId) <$> nextEid'
        LC.Top -> pure (oneEid m', m')
        LC.Bottom -> pure (zeroEid m', m')

    zeroEid, oneEid :: SubexpressionIdMapping -> SubexpressionId
    zeroEid m' =
      case Map.lookup 0 (m' ^. #constants) of
        Just eid -> eid ^. #unOf
        Nothing -> die "zeroEid: no zero subexpression id (this is a compiler bug)"
    oneEid m' =
      case Map.lookup 1 (m' ^. #constants) of
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
        Nothing -> (opId ^. #unOf, m' <> SubexpressionIdMapping mzero mzero mempty mempty mempty (Map.singleton op opId))

    traverseAtom ::
      SubexpressionIdMapping ->
      AtomicLogicConstraint ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traverseAtom m' =
      \case
        LC.Equals x y -> do
          (xId, m'') <- traversePoly m' x
          (yId, m''') <- traversePoly m'' y
          addOp m''' (Equals' xId yId) <$> nextEid'
        LC.LessThan x y -> do
          (xId, m'') <- traversePoly m' x
          (yId, m''') <- traversePoly m'' y
          addOp m''' (LessThan' xId yId) <$> nextEid'

    traversePoly ::
      SubexpressionIdMapping ->
      Polynomial ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traversePoly m' poly =
      case Map.toList (poly ^. #monos) of
        [] -> pure (zeroEid m', m')
        [m] -> traverseMono m' m
        (m : ms) -> do
          (eid, m'') <- traverseMono m' m
          foldM addMono (eid, m'') ms

    addMono ::
      (SubexpressionId, SubexpressionIdMapping) ->
      (PowerProduct, Coefficient) ->
      State S (SubexpressionId, SubexpressionIdMapping)
    addMono (eid, m') m = do
      (eid', m'') <- traverseMono m' m
      addOp m'' (Plus' eid eid') <$> nextEid'

    traverseMono ::
      SubexpressionIdMapping ->
      (PowerProduct, Coefficient) ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traverseMono m' (pp, a) = do
      if Map.null (pp ^. #getPowerProduct)
        then pure (coefficientEid m' a, m')
        else do
          (eid, m'') <- traversePowerProduct m' pp
          addOp m'' (TimesAnd' eid (coefficientEid m'' a)) <$> nextEid'

    traversePowerProduct ::
      SubexpressionIdMapping ->
      PowerProduct ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traversePowerProduct m' pp =
      case Map.toList (pp ^. #getPowerProduct) of
        [] -> pure (oneEid m', m')
        [x] -> traverseVarExponent m' x
        (x : xs) -> do
          (eid, m'') <- traverseVarExponent m' x
          foldM mulVarExponent (eid, m'') xs

    mulVarExponent ::
      (SubexpressionId, SubexpressionIdMapping) ->
      (PolynomialVariable, Exponent) ->
      State S (SubexpressionId, SubexpressionIdMapping)
    mulVarExponent (eid, m') x = do
      (eid', m'') <- traverseVarExponent m' x
      addOp m'' (TimesAnd' eid eid') <$> nextEid'

    traverseVarExponent ::
      SubexpressionIdMapping ->
      (PolynomialVariable, Exponent) ->
      State S (SubexpressionId, SubexpressionIdMapping)
    traverseVarExponent m' (v, e) =
      case e of
        0 -> pure (oneEid m', m')
        1 -> pure (varEid m' v, m')
        _ -> do
          let (e0, r) = e `quotRem` 2
              e1 = e0 + r
          (eid, m'') <- traverseVarExponent m' (v, e0)
          (eid', m''') <- traverseVarExponent m'' (v, e1)
          addOp m''' (TimesAnd' eid eid') <$> nextEid'

    varEid :: SubexpressionIdMapping -> PolynomialVariable -> SubexpressionId
    varEid m' x =
      case Map.lookup x (m' ^. #variables) of
        Just eid -> eid ^. #unOf
        Nothing -> die "varEid: variable lookup failed (this is a compiler bug)"

    coefficientEid ::
      SubexpressionIdMapping ->
      Coefficient ->
      SubexpressionId
    coefficientEid m' a =
      case Map.lookup (a ^. #getCoefficient) (m' ^. #constants) of
        Just eid -> eid ^. #unOf
        Nothing -> die "coefficientEid: coefficient lookup failed (this is a compiler bug)"

    polyVars :: [PolynomialVariable]
    polyVars = Set.toList (getPolynomialVariables c)

    lookupTables :: [[LookupTableColumn]]
    lookupTables = Set.toList (getLookupTables c)

    lookupArguments :: [LookupArgument]
    lookupArguments = c ^. #lookupArguments . #getLookupArguments

    scalars :: [Scalar]
    scalars = Set.toList (getScalars c)

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
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType
getStepTypes c m =
  mconcat
    [ loadStepTypes m,
      lookupStepTypes m,
      constantStepTypes m,
      operatorStepTypes c m
    ]

loadStepTypes ::
  Mapping ->
  Map StepTypeId StepType
loadStepTypes m =
  Map.fromList
    [ (sId, loadStepType m x)
      | (x, sId) <- Map.toList (m ^. #stepTypeIds . #loads)
    ]

loadStepType ::
  Mapping ->
  PolynomialVariable ->
  StepType
loadStepType m x =
  if (x ^. #rowIndex) == 0
    then loadFromSameCaseStepType m (x ^. #colIndex)
    else loadFromDifferentCaseStepType m x

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
  PolynomialVariable ->
  StepType
loadFromDifferentCaseStepType m x =
  StepType
    mempty
    ( LookupArguments
        [ LookupArgument
            P.zero
            [(o, xs), (c, cs)]
        ]
    )
    mempty
  where
    o, c :: InputExpression
    o = InputExpression (P.var' (m ^. #output . #unOutputColumnIndex))
    c =
      InputExpression $
        P.var' (m ^. #caseNumber . #unCaseNumberColumnIndex)
          `P.plus` j

    j :: Polynomial
    j =
      P.constant . fromMaybe (die "loadFromDifferentCaseStepType: relative row index out of range of scalar (this is a compiler bug)") $
        integerToScalar (intToInteger (x ^. #rowIndex . #getRowIndex))

    xs, cs :: LookupTableColumn
    xs = LookupTableColumn (x ^. #colIndex)
    cs = LookupTableColumn (m ^. #caseNumber . #unCaseNumberColumnIndex)

lookupStepTypes ::
  Mapping ->
  Map StepTypeId StepType
lookupStepTypes m =
  Map.fromList
    [ (sId, lookupStepType m t)
      | (t, sId) <- Map.toList (m ^. #stepTypeIds . #lookups)
    ]

-- TODO: what if the lookup argument in the logic circuit is gated?
lookupStepType ::
  Mapping ->
  [LookupTableColumn] ->
  StepType
lookupStepType m t =
  StepType
    mempty
    (LookupArguments [LookupArgument P.zero (zip inputExprs t)])
    mempty
  where
    inputExprs :: [InputExpression]
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
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType
operatorStepTypes c m =
  mconcat
    [ plusStepType m,
      timesStepType m,
      orStepType m,
      notStepType m,
      iffStepType m,
      equalsStepType c m,
      lessThanStepType c m,
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
  orStepType,
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
  lessThanStepType ::
    LogicCircuit ->
    Mapping ->
    Map StepTypeId StepType
equalsStepType c m =
  Map.singleton
    (m ^. #stepTypeIds . #equals . #unOf)
    ( mconcat
        [ StepType
            ( PolynomialConstraints
                [foldl' P.plus P.zero truthVars]
                1
            )
            mempty
            mempty,
          byteDecompositionCheck c m
        ]
    )
  where
    truthVars :: [Polynomial]
    truthVars =
      P.var' . (^. #unTruthValueColumnIndex) . snd
        <$> (m ^. #byteDecomposition . #bytes)
lessThanStepType c m =
  Map.singleton
    (m ^. #stepTypeIds . #lessThan . #unOf)
    ( mconcat
        [ StepType
            ( PolynomialConstraints
                [ P.var' (m ^. #byteDecomposition . #sign . #unSignColumnIndex),
                  P.one
                    `P.minus` foldl'
                      (\x y -> x `P.plus` (y `P.minus` (x `P.times` y)))
                      P.zero
                      [ P.var' (snd i ^. #unTruthValueColumnIndex)
                        | i <- m ^. #byteDecomposition . #bytes
                      ]
                ]
                ( PolynomialDegreeBound
                    (max 1 (length (m ^. #byteDecomposition . #bytes)))
                )
            )
            mempty
            mempty,
          byteDecompositionCheck c m
        ]
    )

byteDecompositionCheck ::
  LogicCircuit ->
  Mapping ->
  StepType
byteDecompositionCheck c m =
  StepType
    ( PolynomialConstraints
        [ (v0 `P.minus` v1)
            `P.minus` ( ((P.constant 2 `P.times` s) `P.minus` P.one)
                          `P.times` foldl'
                            P.plus
                            P.zero
                            (zipWith P.times byteCoefs byteVars)
                      )
        ]
        (PolynomialDegreeBound 2)
    )
    (byteRangeAndTruthChecks m <> signRangeCheck m)
    (truthTables m)
  where
    (i0, i1) = firstTwoInputs m
    v0 = P.var' (i0 ^. #unInputColumnIndex)
    v1 = P.var' (i1 ^. #unInputColumnIndex)
    s = P.var' (m ^. #byteDecomposition . #sign . #unSignColumnIndex)

    byteCoefs, byteVars :: [Polynomial]
    byteCoefs =
      P.constant . fromMaybe (die "truthTables: byte coefficient is not in range of scalar (this is a compiler bug)") . integerToScalar
        <$> [2 ^ i | i <- [0 .. getByteDecompositionLength (m ^. #byteDecomposition . #bits) c]]
    byteVars =
      P.var' . (^. #unByteColumnIndex) . fst
        <$> (m ^. #byteDecomposition . #bytes)

byteRangeAndTruthChecks ::
  Mapping ->
  LookupArguments
byteRangeAndTruthChecks m =
  LookupArguments
    [ LookupArgument
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

signRangeCheck ::
  Mapping ->
  LookupArguments
signRangeCheck m =
  LookupArguments
    [ LookupArgument
        P.zero
        [ ( InputExpression (P.var' (m ^. #byteDecomposition . #sign . #unSignColumnIndex)),
            LookupTableColumn (m ^. #truthTable . #zeroIndicatorColumnIndex . #unZeroIndicatorColumnIndex)
          )
        ]
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
    zeroIndicator = 1 : replicate (length byteRange - 1) 0

maybeToSet :: Ord a => Maybe a -> Set a
maybeToSet = maybe mempty Set.singleton

getSubexpressionIdSet ::
  SubexpressionIdMapping ->
  Set SubexpressionId
getSubexpressionIdSet m =
  mconcat
    [ maybeToSet ((m ^. #void) <&> (^. #unOf)),
      maybeToSet ((m ^. #result) <&> (^. #unResultExpressionId)),
      Set.fromList (Map.elems (m ^. #variables) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #lookups) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #constants) <&> (^. #unOf)),
      Set.fromList (Map.elems (m ^. #operations) <&> (^. #unOf))
    ]

getSubexpressionLinks ::
  Mapping ->
  Set SubexpressionLink
getSubexpressionLinks = todo

getResultExpressionId ::
  Mapping ->
  ResultExpressionId
getResultExpressionId m =
  case m ^. #subexpressionIds . #result of
    Just x -> x
    Nothing -> die "getResultExpressionId: no result (this is a compiler bug)"

maxStepsPerCase ::
  Set SubexpressionId ->
  Scalar
maxStepsPerCase =
  fromMaybe (die "maxStepsPerCase: out of range of scalar (this is a compiler bug)")
    . integerToScalar
    . intToInteger
    . Set.size

todo :: a
todo = todo
