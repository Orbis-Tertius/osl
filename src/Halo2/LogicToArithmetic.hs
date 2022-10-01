{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}


module Halo2.LogicToArithmetic
  ( eval
  , translateLogicGate
  , byteDecompositionGate
  , getLayout
  , getSignRangeCheck
  , getByteRangeAndTruthTableCheck
  ) where


import Control.Monad (forM, replicateM)
import Control.Monad.State (State, get, put, runState)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Halo2.Prelude
import Halo2.ByteDecomposition (countBytes)
import qualified Halo2.Coefficient as C
import qualified Halo2.Polynomial as P
import qualified Halo2.FiniteField as F
import Halo2.Types.BitsPerByte (BitsPerByte (..))
import Halo2.Types.Circuit (LogicCircuit)
import Halo2.Types.ColumnIndex (ColumnIndex (..))
import Halo2.Types.ColumnTypes (ColumnTypes (..))
import Halo2.Types.ColumnType (ColumnType (Fixed))
import Halo2.Types.FiniteField (FiniteField (..))
import Halo2.Types.FixedBound (FixedBound (..))
import Halo2.Types.InputExpression (InputExpression (..))
import Halo2.Types.LogicConstraint (LogicConstraint (..), AtomicLogicConstraint (..), atomicConstraintArgs)
import Halo2.Types.LogicToArithmeticColumnLayout (LogicToArithmeticColumnLayout (..), TruthValueColumnIndex (..), AtomAdvice (..), ByteColumnIndex (..), ByteRangeColumnIndex (..), ZeroIndicatorColumnIndex (..), TruthTableColumnIndices (..), SignColumnIndex (..))
import Halo2.Types.LookupArgument (LookupArgument (..))
import Halo2.Types.LookupTableColumn (LookupTableColumn (..))
import Halo2.Types.Polynomial (Polynomial (..))
import Halo2.Types.PolynomialVariable (PolynomialVariable (..))


translateLogicGate
  :: FiniteField
  -> LogicToArithmeticColumnLayout
  -> LogicConstraint
  -> Maybe Polynomial
translateLogicGate f layout p =
  P.minus f <$> eval f layout p <*> pure P.one


byteDecompositionGate
  :: FiniteField
  -> LogicToArithmeticColumnLayout
  -> AtomicLogicConstraint
  -> Maybe Polynomial
byteDecompositionGate f layout c =
  let (a, b) = atomicConstraintArgs c
  in do
    advice <- Map.lookup c (layout ^. #atomAdvice)
    pure $ P.minus f (P.minus f a b)
       (P.times f
         (P.var (PolynomialVariable
                   (advice ^. #sign . #unSignColumnIndex)
                   0))
         (P.sum f
           [ P.times f (P.constant (2 ^ j)) d
           | (j, d) :: (Integer, Polynomial) <- zip [0..]
               (reverse (P.var . flip PolynomialVariable 0
                       . unByteColumnIndex
                     <$> (advice ^. #bytes)))
           ]))


eval :: FiniteField
     -> LogicToArithmeticColumnLayout
     -> LogicConstraint
     -> Maybe Polynomial
eval f layout =
  \case
    Atom (Equals p q) -> do
      advice <- Map.lookup (Equals p q) (layout ^. #atomAdvice)
      pure $ P.times f (signPoly f advice) (eqMono advice)
    Atom (LessThan p q) -> do
      advice <- Map.lookup (LessThan p q) (layout ^. #atomAdvice)
      pure $ P.times f (signPoly f advice)
             (some f (unTruthValueColumnIndex <$> advice ^. #truthValue))
    Not p -> P.minus f P.one <$> rec p
    And p q -> P.times f <$> rec p <*> rec q
    Or p q ->
      let a = rec p
          b = rec q in
      P.plus f <$> a <*> (P.minus f <$> b <*> (P.times f <$> a <*> b))
  where
    rec = eval f layout


signPoly :: FiniteField -> AtomAdvice -> Polynomial
signPoly f advice =
  P.times f (P.constant (F.half f))
    (P.plus f (P.constant F.one)
      (P.var (PolynomialVariable
                (advice ^. #sign . #unSignColumnIndex)
                0)))


eqMono :: AtomAdvice -> Polynomial
eqMono advice =
  P.multilinearMonomial C.one
    $ flip PolynomialVariable 0 . unTruthValueColumnIndex
       <$> advice ^. #truthValue


some :: FiniteField -> [ColumnIndex] -> Polynomial
some _ [] = P.zero
some f (x:xs) =
  let a = P.var (PolynomialVariable x 0)
      b = some f xs in
  P.plus f a (P.minus f b (P.times f a b))


getLayout :: BitsPerByte
  -> FiniteField
  -> LogicCircuit
  -> LogicToArithmeticColumnLayout
getLayout bits f lc =
  let i0 = ColumnIndex . length
         $ lc ^. #columnTypes . #getColumnTypes
  in fst $ runState (getLayoutM bits f lc) i0


getLayoutM :: BitsPerByte
  -> FiniteField
  -> LogicCircuit
  -> State ColumnIndex LogicToArithmeticColumnLayout
getLayoutM bits f lc = do
  tabi0 <- ByteRangeColumnIndex <$> nextColIndex
  tabi1 <- ZeroIndicatorColumnIndex <$> nextColIndex
  atomAdvices <- fmap Map.fromList .
    forM (Set.toList (getAtomicConstraints lc)) $ \ac ->
      (ac,) <$> getAtomAdviceM bits f
  let colTypes = lc ^. #columnTypes
              <> ColumnTypes [Fixed, Fixed]
      lcCols = Set.fromList . fmap ColumnIndex
        $ [ 0 .. length (lc ^. #columnTypes . #getColumnTypes)
                 - 1 ]
  pure $ LogicToArithmeticColumnLayout
    colTypes
    lcCols
    atomAdvices
    (TruthTableColumnIndices tabi0 tabi1)


getAtomAdviceM :: BitsPerByte
  -> FiniteField
  -> State ColumnIndex AtomAdvice
getAtomAdviceM bits (FiniteField fieldSize) = do
  AtomAdvice
    <$> (SignColumnIndex <$> nextColIndex)
    <*> (replicateM n (ByteColumnIndex <$> nextColIndex))
    <*> (replicateM n (TruthValueColumnIndex <$> nextColIndex))
  where n = countBytes bits (FixedBound fieldSize)


getAtomicConstraints :: LogicCircuit -> Set AtomicLogicConstraint
getAtomicConstraints lc =
  Set.unions $ getAtomicSubformulas
    <$> lc ^. #gateConstraints . #constraints


getAtomicSubformulas :: LogicConstraint -> Set AtomicLogicConstraint
getAtomicSubformulas =
  \case
    Atom a -> Set.singleton a
    Not p -> rec p
    And p q -> rec p <> rec q
    Or p q -> rec p <> rec q
  where
    rec = getAtomicSubformulas


getSignRangeCheck :: FiniteField
  -> LogicToArithmeticColumnLayout
  -> AtomicLogicConstraint
  -> Maybe LookupArgument
getSignRangeCheck f layout c = do
  advice <- Map.lookup c (layout ^. #atomAdvice)
  pure . LookupArgument
    $ [( InputExpression (signPoly f advice)
       , LookupTableColumn $ layout ^. #truthTable
           . #zeroIndicatorColumnIndex
           . #unZeroIndicatorColumnIndex
       )]


getByteRangeAndTruthTableCheck :: LogicToArithmeticColumnLayout
  -> AtomicLogicConstraint
  -> Maybe LookupArgument
getByteRangeAndTruthTableCheck = todo


todo :: a
todo = todo


nextColIndex :: State ColumnIndex ColumnIndex
nextColIndex = do
  i <- get
  put (i+1)
  pure i
