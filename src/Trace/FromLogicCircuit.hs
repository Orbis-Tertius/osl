{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
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
import Control.Lens ((<&>))
import Control.Monad (replicateM)
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
import Halo2.Types.ColumnIndex (ColumnIndex (ColumnIndex))
import Halo2.Types.ColumnType (ColumnType (Advice))
import Halo2.Types.ColumnTypes (ColumnTypes (ColumnTypes))
import Halo2.Types.InputExpression (InputExpression (InputExpression))
import Halo2.Types.LookupArgument (LookupArgument (LookupArgument))
import Halo2.Types.LookupArguments (LookupArguments (LookupArguments))
import Halo2.Types.LookupTableColumn (LookupTableColumn (LookupTableColumn))
import Halo2.Types.Polynomial (Polynomial)
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable)
import Halo2.Types.RowCount (RowCount (RowCount))
import OSL.Types.Arity (Arity (Arity))
import Stark.Types.Scalar (Scalar, integerToScalar)
import Trace.Types (CaseNumberColumnIndex (..), InputColumnIndex (..), NumberOfCases (NumberOfCases), OutputColumnIndex (..), ResultExpressionId, StepIndicatorColumnIndex (..), StepType (StepType), StepTypeColumnIndex (..), StepTypeId (StepTypeId), SubexpressionId, SubexpressionLink, TraceType (TraceType))

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
    links
    resultId
    (mapping ^. #caseNumber)
    (mapping ^. #stepType)
    (mapping ^. #stepIndicator)
    (mapping ^. #inputs)
    (mapping ^. #output)
    (NumberOfCases (rowCount ^. #getRowCount))
    (rowCount * RowCount (maxStepsPerCase colTypes' stepTypes subexprs links resultId))
  where
    rowCount = c ^. #rowCount

    mapping = getMapping bitsPerByte c

    colTypes' = getColumnTypes c mapping

    stepTypes = getStepTypes mapping

    (subexprs, links, resultId) = getSubexpressions c mapping stepTypes

-- TODO: let the columns be reused where possible
data Mapping = Mapping
  { caseNumber :: CaseNumberColumnIndex,
    stepType :: StepTypeColumnIndex,
    stepIndicator :: StepIndicatorColumnIndex,
    inputs :: [InputColumnIndex],
    output :: OutputColumnIndex,
    byteDecomposition :: ByteDecompositionMapping,
    truthTable :: TruthTableColumnIndices,
    stepTypeIds :: StepTypeIdMapping
  }
  deriving (Generic)

data ByteDecompositionMapping = ByteDecompositionMapping
  { sign :: SignColumnIndex,
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
  | Times
  | And
  | Or
  | Not
  | Iff
  | Equals
  | LessThan
  | Void

type StepTypeIdOf :: Operator -> Type
newtype StepTypeIdOf a = StepTypeIdOf {unOf :: StepTypeId}
  deriving (Generic)

data StepTypeIdMapping = StepTypeIdMapping
  { loads :: Map PolynomialVariable StepTypeId,
    lookups :: Map [LookupTableColumn] StepTypeId,
    constants :: Map Scalar StepTypeId,
    plus :: StepTypeIdOf Plus,
    times :: StepTypeIdOf Times,
    and :: StepTypeIdOf And,
    or :: StepTypeIdOf Or,
    not :: StepTypeIdOf Not,
    iff :: StepTypeIdOf Iff,
    equals :: StepTypeIdOf Equals,
    lessThan :: StepTypeIdOf LessThan,
    voidT :: StepTypeIdOf Void
  }
  deriving (Generic)

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
    nextStepTypeId :: StepTypeId
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

    nextCol :: State S ColumnIndex
    nextCol = do
      S i j <- get
      put (S (i + 1) j)
      pure i

    nextSid :: State S StepTypeId
    nextSid = do
      S i j <- get
      put (S i (j + 1))
      pure j

    nextSid' :: State S (StepTypeIdOf a)
    nextSid' = StepTypeIdOf <$> nextSid

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
        <*> ( ByteDecompositionMapping
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
                <*> (nextSid' :: State S (StepTypeIdOf Times))
                <*> (nextSid' :: State S (StepTypeIdOf And))
                <*> (nextSid' :: State S (StepTypeIdOf Or))
                <*> (nextSid' :: State S (StepTypeIdOf Not))
                <*> (nextSid' :: State S (StepTypeIdOf Iff))
                <*> (nextSid' :: State S (StepTypeIdOf Equals))
                <*> (nextSid' :: State S (StepTypeIdOf LessThan))
                <*> (nextSid' :: State S (StepTypeIdOf Void))
            )

    polyVars :: [PolynomialVariable]
    polyVars = Set.toList (getPolynomialVariables c)

    lookupTables :: [[LookupTableColumn]]
    lookupTables = Set.toList (getLookupTables c)

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
  Mapping ->
  Map StepTypeId StepType
getStepTypes m =
  mconcat
    [ loadStepTypes m,
      lookupStepTypes m,
      constantStepTypes m,
      operatorStepTypes m
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
  (PolynomialConstraints
    [P.minus (P.constant x)
      (P.var' (m ^. #output . #unOutputColumnIndex))]
    1)
  mempty
  mempty

operatorStepTypes ::
  Mapping ->
  Map StepTypeId StepType
operatorStepTypes m =
  mconcat
    [ plusStepType m,
      timesStepType m,
      andStepType m,
      orStepType m,
      notStepType m,
      iffStepType m,
      equalsStepType m,
      lessThanStepType m,
      voidStepType m
    ]

firstTwoInputs ::
  Mapping ->
  (InputColumnIndex, InputColumnIndex)
firstTwoInputs m =
  case m ^. #inputs of
    (i0:i1:_) -> (i0,i1)
    _ -> die "firstTwoInputs: there are not two inputs (this is a compiler bug)"

plusStepType,
  timesStepType,
  andStepType,
  orStepType,
  notStepType,
  iffStepType,
  equalsStepType,
  lessThanStepType,
  voidStepType ::
    Mapping ->
    Map StepTypeId StepType

plusStepType m =
  Map.singleton
  (m ^. #stepTypeIds . #plus . #unOf)
  (StepType
    (PolynomialConstraints
      [P.minus (P.var' (m ^. #output . #unOutputColumnIndex))
        (P.plus (P.var' (i0 ^. #unInputColumnIndex))
                (P.var' (i1 ^. #unInputColumnIndex)))]
      1)
    mempty
    mempty)
  where
    (i0, i1) = firstTwoInputs m

timesStepType m =
  Map.singleton
  (m ^. #stepTypeIds . #times . #unOf)
  (StepType
    (PolynomialConstraints
      [P.minus (P.var' (m ^. #output . #unOutputColumnIndex))
        (P.times (P.var' (i0 ^. #unInputColumnIndex))
                 (P.var' (i1 ^. #unInputColumnIndex)))]
      2)
    mempty
    mempty)
  where
    (i0, i1) = firstTwoInputs m

andStepType = todo
orStepType = todo
notStepType = todo
iffStepType = todo
equalsStepType = todo
lessThanStepType = todo
voidStepType m =
  Map.singleton (m ^. #stepTypeIds . #voidT . #unOf) mempty

getSubexpressions ::
  LogicCircuit ->
  Mapping ->
  Map StepTypeId StepType ->
  ( Set SubexpressionId,
    Set SubexpressionLink,
    ResultExpressionId
  )
getSubexpressions = todo

maxStepsPerCase ::
  ColumnTypes ->
  Map StepTypeId StepType ->
  Set SubexpressionId ->
  Set SubexpressionLink ->
  ResultExpressionId ->
  Scalar
maxStepsPerCase = todo

todo :: a
todo = todo
