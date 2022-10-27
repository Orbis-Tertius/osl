{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.LogicToArithmetic
  ( eval,
    translateLogicGate,
    byteDecompositionGate,
    getLayout,
    getSignRangeCheck,
    getByteRangeAndTruthTableChecks,
    logicToArithmeticCircuit,
  )
where

import Cast (intToInteger)
import Control.Monad (forM, replicateM)
import Control.Monad.State (State, evalState, get, put)
import Crypto.Number.Basic (numBits)
import Data.List (foldl', sum)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Halo2.ByteDecomposition (countBytes)
import qualified Halo2.Polynomial as P
import Halo2.Prelude
import Halo2.TruthTable (getByteRangeColumn, getZeroIndicatorColumn)
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Circuit (ArithmeticCircuit, Circuit (..), LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex (..))
import Halo2.Types.ColumnType (ColumnType (Advice, Fixed))
import qualified Halo2.Types.ColumnTypes as ColumnTypes
import Halo2.Types.FixedBound (FixedBound (..))
import Halo2.Types.FixedValues (FixedValues (..))
import Halo2.Types.InputExpression (InputExpression (..))
import Halo2.Types.LogicConstraint (AtomicLogicConstraint (..), LogicConstraint (..), atomicConstraintArgs)
import Halo2.Types.LogicToArithmeticColumnLayout (AtomAdvice (..), ByteColumnIndex (..), ByteRangeColumnIndex (..), LogicToArithmeticColumnLayout (..), SignColumnIndex (..), TruthTableColumnIndices (..), TruthValueColumnIndex (..), ZeroIndicatorColumnIndex (..))
import Halo2.Types.LookupArgument (LookupArgument (..))
import Halo2.Types.LookupArguments (LookupArguments (..))
import Halo2.Types.LookupTableColumn (LookupTableColumn (..))
import Halo2.Types.Polynomial (Polynomial (..))
import Halo2.Types.PolynomialConstraints (PolynomialConstraints (..))
import Halo2.Types.PolynomialDegreeBound (PolynomialDegreeBound (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))
import Halo2.Types.RowCount (RowCount)
import Stark.Types.Scalar (half)

translateLogicGate ::
  LogicToArithmeticColumnLayout ->
  LogicConstraint ->
  Maybe Polynomial
translateLogicGate layout p =
  P.minus <$> eval layout p <*> pure P.one

byteDecompositionGate ::
  LogicToArithmeticColumnLayout ->
  AtomicLogicConstraint ->
  Maybe Polynomial
byteDecompositionGate layout c =
  let (a, b) = atomicConstraintArgs c
   in do
        advice <- Map.lookup c (layout ^. #atomAdvice)
        pure $
          (a `P.minus` b)
            `P.minus` ( P.var
                          ( PolynomialVariable
                              (advice ^. #sign . #unSignColumnIndex)
                              0
                          )
                          `P.times` P.sum
                            [ P.constant (2 ^ j) `P.times` d
                              | (j, d) :: (Integer, Polynomial) <-
                                  zip
                                    [0 ..]
                                    ( reverse
                                        ( P.var
                                            . flip PolynomialVariable 0
                                            . unByteColumnIndex
                                            <$> (advice ^. #bytes)
                                        )
                                    )
                            ]
                      )

eval ::
  LogicToArithmeticColumnLayout ->
  LogicConstraint ->
  Maybe Polynomial
eval layout =
  \case
    Atom (Equals p q) -> do
      advice <- Map.lookup (Equals p q) (layout ^. #atomAdvice)
      pure $ signPoly advice `P.times` eqMono advice
    Atom (LessThan p q) -> do
      advice <- Map.lookup (LessThan p q) (layout ^. #atomAdvice)
      pure $
        signPoly advice
          `P.times` some (unTruthValueColumnIndex <$> advice ^. #truthValue)
    Not p -> P.minus P.one <$> rec p
    And p q -> P.times <$> rec p <*> rec q
    Or p q ->
      let a = rec p
          b = rec q
       in P.plus <$> a <*> (P.minus <$> b <*> (P.times <$> a <*> b))
    Iff p q ->
      let a = rec p
          b = rec q
          c =
            P.minus P.one
              <$> (P.minus <$> a <*> b)
       in P.times <$> c <*> c
    Top -> pure (P.constant 1)
    Bottom -> pure (P.constant 0)
  where
    rec = eval layout

signPoly :: AtomAdvice -> Polynomial
signPoly advice =
  P.constant half
    `P.times` ( P.one
                  `P.plus` P.var
                    ( PolynomialVariable
                        (advice ^. #sign . #unSignColumnIndex)
                        0
                    )
              )

eqMono :: AtomAdvice -> Polynomial
eqMono advice =
  P.multilinearMonomial 1 $
    flip PolynomialVariable 0 . unTruthValueColumnIndex
      <$> advice ^. #truthValue

some :: [ColumnIndex] -> Polynomial
some [] = P.zero
some (x : xs) =
  let a = P.var (PolynomialVariable x 0)
      b = some xs
   in a `P.plus` (b `P.minus` (a `P.times` b))

getLayout ::
  BitsPerByte ->
  LogicCircuit ->
  LogicToArithmeticColumnLayout
getLayout bits lc =
  let i0 =
        ColumnIndex . length $
          lc ^. #columnTypes . #getColumnTypes
   in evalState (getLayoutM bits lc) i0

getLayoutM ::
  BitsPerByte ->
  LogicCircuit ->
  State ColumnIndex LogicToArithmeticColumnLayout
getLayoutM bits lc = do
  tabi0 <- ByteRangeColumnIndex <$> nextColIndex
  tabi1 <- ZeroIndicatorColumnIndex <$> nextColIndex
  atomAdvices <- fmap Map.fromList
    . forM (Set.toList (getAtomicConstraints lc))
    $ \ac ->
      (ac,) <$> getAtomAdviceM bits
  let colTypes =
        lc ^. #columnTypes -- TODO: include the remaining columns
          <> ColumnTypes.fromList (replicate (sum (countAtomAdviceCols <$> atomAdvices)) Advice)
          <> ColumnTypes.fromList [Fixed, Fixed]
      lcCols =
        Set.fromList . fmap ColumnIndex $
          [ 0
            .. length (lc ^. #columnTypes . #getColumnTypes)
              - 1
          ]
  pure $
    LogicToArithmeticColumnLayout
      colTypes
      lcCols
      atomAdvices
      (TruthTableColumnIndices tabi0 tabi1)

countAtomAdviceCols :: AtomAdvice -> Int
countAtomAdviceCols a =
  1 + length (a ^. #bytes) + length (a ^. #truthValue)

getAtomAdviceM ::
  BitsPerByte ->
  State ColumnIndex AtomAdvice
getAtomAdviceM bits = do
  AtomAdvice
    <$> (SignColumnIndex <$> nextColIndex)
    <*> replicateM n (ByteColumnIndex <$> nextColIndex)
    <*> replicateM n (TruthValueColumnIndex <$> nextColIndex)
  where
    n = countBytes bits (FixedBound maxBound)

getAtomicConstraints :: LogicCircuit -> Set AtomicLogicConstraint
getAtomicConstraints lc =
  Set.unions $
    getAtomicSubformulas
      <$> lc ^. #gateConstraints . #constraints

getAtomicSubformulas :: LogicConstraint -> Set AtomicLogicConstraint
getAtomicSubformulas =
  \case
    Atom a -> Set.singleton a
    Not p -> rec p
    And p q -> rec p <> rec q
    Or p q -> rec p <> rec q
    Iff p q -> rec p <> rec q
    Top -> mempty
    Bottom -> mempty
  where
    rec = getAtomicSubformulas

getSignRangeCheck ::
  LogicToArithmeticColumnLayout ->
  AtomicLogicConstraint ->
  Maybe LookupArgument
getSignRangeCheck layout c = do
  advice <- Map.lookup c (layout ^. #atomAdvice)
  pure . LookupArgument P.zero $
    [ ( InputExpression (signPoly advice),
        LookupTableColumn $
          layout
            ^. #truthTable
              . #zeroIndicatorColumnIndex
              . #unZeroIndicatorColumnIndex
      )
    ]

getByteRangeAndTruthTableChecks ::
  LogicToArithmeticColumnLayout ->
  AtomicLogicConstraint ->
  Maybe LookupArgument
getByteRangeAndTruthTableChecks layout c = do
  advice <- Map.lookup c (layout ^. #atomAdvice)
  let b0 =
        layout
          ^. #truthTable
            . #zeroIndicatorColumnIndex
            . #unZeroIndicatorColumnIndex
      b1 =
        layout
          ^. #truthTable
            . #byteRangeColumnIndex
            . #unByteRangeColumnIndex
  pure . LookupArgument (P.constant 0) $ do
    (byteCol, truthValCol) <-
      zip
        (advice ^. #bytes)
        (advice ^. #truthValue)
    let delta = P.var (PolynomialVariable (truthValCol ^. #unTruthValueColumnIndex) 0)
        beta = P.var (PolynomialVariable (byteCol ^. #unByteColumnIndex) 0)
    [ (InputExpression delta, LookupTableColumn b0),
      (InputExpression beta, LookupTableColumn b1)
      ]

nextColIndex :: State ColumnIndex ColumnIndex
nextColIndex = do
  i <- get
  put (i + 1)
  pure i

getPolyDegreeBound :: Polynomial -> PolynomialDegreeBound
getPolyDegreeBound p =
  PolynomialDegreeBound $
    2 ^ numBits (intToInteger (P.degree p))

logicToArithmeticCircuit ::
  BitsPerByte ->
  RowCount ->
  LogicCircuit ->
  Maybe ArithmeticCircuit
logicToArithmeticCircuit bits rows lc = do
  let layout = getLayout bits lc
      atoms = Set.toList (getAtomicConstraints lc)
  translatedGates <-
    forM (lc ^. #gateConstraints . #constraints) $
      translateLogicGate layout
  decompositionGates <-
    forM atoms $ byteDecompositionGate layout
  let polyGates = translatedGates <> decompositionGates
      degreeBound =
        foldl'
          max
          0
          (getPolyDegreeBound <$> polyGates)
  signChecks <-
    forM atoms $ getSignRangeCheck layout
  rangeAndTruthChecks <-
    forM atoms $ getByteRangeAndTruthTableChecks layout
  pure $
    Circuit
      (layout ^. #columnTypes)
      (lc ^. #equalityConstrainableColumns)
      (PolynomialConstraints polyGates degreeBound)
      ( mempty (lc ^. #lookupArguments)
          <> LookupArguments signChecks
          <> LookupArguments rangeAndTruthChecks
      )
      rows
      (lc ^. #equalityConstraints)
      ( (lc ^. #fixedValues)
          <> FixedValues
            ( Map.singleton
                ( layout
                    ^. #truthTable
                      . #byteRangeColumnIndex
                      . #unByteRangeColumnIndex
                )
                (getByteRangeColumn bits rows)
            )
          <> FixedValues
            ( Map.singleton
                ( layout
                    ^. #truthTable
                      . #zeroIndicatorColumnIndex
                      . #unZeroIndicatorColumnIndex
                )
                (getZeroIndicatorColumn rows)
            )
      )
