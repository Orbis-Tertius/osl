{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module OSL.Spec.SudokuSpec (spec) where

import Control.Lens ((^.))
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import Die (die)
import OSL.ArgumentForm (getArgumentForm)
import OSL.LoadContext (loadContext)
import OSL.Satisfaction (satisfiesSimple)
import OSL.SimplifyType (simplifyType, complexifyValueUnsafe)
import OSL.Types.Argument (Argument (Argument), Statement (Statement), Witness (Witness))
import OSL.Types.ArgumentForm (ArgumentForm (ArgumentForm), StatementType (StatementType), WitnessType (WitnessType))
import OSL.Types.FileName (FileName (FileName))
import OSL.Types.OSL (ValidContext, ContextType (Global), Declaration (Defined), Name (Sym), Type (Product, NamedType, Fin, F))
import OSL.Types.Value (Value (Fun, Maybe'', To', Fin', Pair'))
import OSL.ValidContext (getNamedTermUnsafe)
import Stark.Types.Scalar (integerToScalar)
import Test.Syd (Spec, describe, liftIO, expectationFailure, it, shouldBe)
import Text.Parsec (SourcePos)

spec :: Spec
spec =
  describe "Sudoku" $ do
    mctx <- loadContext (FileName "examples/sudoku.osl")
    case mctx of
      Left err -> liftIO . expectationFailure $ show err
      Right c -> spec' c

spec' :: ValidContext 'Global SourcePos -> Spec
spec' c = do
  argumentFormSpec c

argumentFormSpec :: ValidContext 'Global SourcePos -> Spec
argumentFormSpec c = do
  it "has the correct argument form" $
    case Map.lookup (Sym "problemIsSolvable")
           (c ^. #unValidContext) of
      Just (Defined t x) -> do
        getArgumentForm c t x `shouldBe`
          Right (ArgumentForm
                   (StatementType complexStatementType)
                   (WitnessType complexWitnessType))
      _ ->
        liftIO . expectationFailure $
          "problemIsSolvable definition not found"

  it "has the correct simplified statement type" $
    simplifyType complexStatementType `shouldBe` Just simpleStatementType

  it "has the correct simplified witness type" $
    simplifyType complexWitnessType `shouldBe` Just simpleWitnessType

  it "is satisfied on a true example" $
    satisfiesSimple c (getNamedTermUnsafe c "problemIsSolvable") (exampleArgument c)
      `shouldBe` Right True

exampleArgument :: ValidContext 'Global ann -> Argument
exampleArgument c =
  Argument
  (Statement (complexifyValueUnsafe c complexStatementType
    (problemToValue exampleProblem)))
  (Witness (complexifyValueUnsafe c complexWitnessType
    (sudokuWitnessToValue exampleWitness)))

exampleProblem :: Problem
exampleProblem = todo

exampleWitness :: SudokuWitness
exampleWitness = todo

todo :: a
todo = todo

newtype Digit = Digit Integer
  deriving (Eq, Ord, Num, Enum)

newtype Row = Row Integer
  deriving (Eq, Ord, Num, Enum)

newtype Col = Col Integer
  deriving (Eq, Ord, Num, Enum)

newtype Cell = Cell (Row, Col)

newtype Problem = Problem (Cell -> Maybe Digit)

newtype Solution = Solution (Cell -> Digit)

newtype X = X Integer
  deriving (Eq, Ord, Num, Enum)

newtype Y = Y Integer
  deriving (Eq, Ord, Num, Enum)

newtype Square = Square (X, Y)
  deriving (Eq, Ord)

newtype SquareCell = SquareCell (X, Y)
  deriving (Eq, Ord)

data SudokuWitness =
  SudokuWitness
  { solution :: Solution,
    rowPermutations :: Map Row (Map Digit Col),
    colPermutations :: Map Col (Map Digit Row),
    squarePermutations :: Map Square (Map Digit SquareCell)
  }

createWitness :: Solution -> Maybe SudokuWitness
createWitness s =
  SudokuWitness s
    <$> getRowPermutations s
    <*> getColPermutations s
    <*> getSquarePermutations s

getRowPermutations :: Solution -> Maybe (Map Row (Map Digit Col))
getRowPermutations s =
  mconcat <$> sequence
    [ Map.singleton r <$> getRowPermutation s r | r <- [0..8] ]

getRowPermutation :: Solution -> Row -> Maybe (Map Digit Col)
getRowPermutation (Solution s) r =
  Map.fromList <$> sequence
    [ (v,) <$> find ((== v) . (\c -> s (Cell (r, c)))) [0..8]
    | v <- [0..8]
    ]

getColPermutations :: Solution -> Maybe (Map Col (Map Digit Row))
getColPermutations s =
  mconcat <$> sequence
    [ Map.singleton c <$> getColPermutation s c | c <- [0..8] ]

getColPermutation :: Solution -> Col -> Maybe (Map Digit Row)
getColPermutation (Solution s) c =
  Map.fromList <$> sequence
    [ (v,) <$> find ((== v) . (\r -> s (Cell (r, c)))) [0..8]
    | v <- [0..8]
    ]

getSquarePermutations :: Solution -> Maybe (Map Square (Map Digit SquareCell))
getSquarePermutations s =
  mconcat <$> sequence
    [ Map.singleton sq <$> getSquarePermutation s sq
    | sq <- Square <$> ((,) <$> [0..2] <*> [0..2])
    ]

getSquarePermutation :: Solution -> Square -> Maybe (Map Digit SquareCell)
getSquarePermutation (Solution s) sq =
  Map.fromList <$> sequence
    [ (v,) <$> find ((== v) . (\c -> s (getCell sq c)))
        (SquareCell <$> ((,) <$> [0..2] <*> [0..2]))
    | v <- [0..8]
    ]

getCell :: Square -> SquareCell -> Cell
getCell (Square (X sx, Y sy)) (SquareCell (X x, Y y)) =
  Cell (Row (3 * sy + y), Col (3 * sx + x))

complexStatementType :: Type ()
complexStatementType =
  Product () (NamedType () (Sym "Problem")) (Fin () 1)

simpleStatementType :: Type ()
simpleStatementType = NamedType () (Sym "Problem")

problemToValue :: Problem -> Value
problemToValue (Problem p) =
  To' "Problem" . Fun . Map.fromList $
    [ (cellToValue c, Maybe'' (digitToValue <$> p c))
    | c <- Cell <$> ((,) <$> [0..8] <*> [0..8])
    ]

digitToValue :: Digit -> Value
digitToValue (Digit d) =
  maybe (die "digitToValue: out of range")
    (To' "Digit" . Fin')
    (integerToScalar d)

cellToValue :: Cell -> Value
cellToValue (Cell (r, c)) =
  To' "Cell" (Pair' (rowToValue r) (colToValue c))

rowToValue :: Row -> Value
rowToValue (Row r) =
  maybe (die "rowToValue: out of range")
    (To' "Row" . Fin')
    (integerToScalar r)

colToValue :: Col -> Value
colToValue (Col c) =
  maybe (die "colToValue: out of range")
    (To' "Col" . Fin')
    (integerToScalar c)

complexWitnessType :: Type ()
complexWitnessType =
  Product ()
    (NamedType () "Solution")
    (Product ()
      (F () Nothing
        (NamedType () "Cell")
        (Product () (Fin () 1) (Fin () 1)))
      (Product ()
        (Product ()
          (F () Nothing
            (NamedType () "Row")
            (F () Nothing
              (NamedType () "Digit")
              (Product ()
                (NamedType () "Col")
                (Fin () 1))))
          (F () Nothing
            (NamedType () "Col")
            (F () Nothing
              (NamedType () "Digit")
              (Product ()
                (NamedType () "Row")
                (Fin () 1)))))
        (F () Nothing
          (NamedType () "Square")
          (F () Nothing
            (NamedType () "Digit")
            (Product ()
              (NamedType () "SquareCell")
              (Fin () 1))))))

simpleWitnessType :: Type ()
simpleWitnessType =
  Product ()
    (NamedType () "Solution")
    (Product ()
      (Product ()
        (F () Nothing
          (NamedType () "Row")
          (F () Nothing
            (NamedType () "Digit")
            (NamedType () "Col")))
        (F () Nothing
          (NamedType () "Col")
          (F () Nothing
            (NamedType () "Digit")
            (NamedType () "Row"))))
      (F () Nothing
        (NamedType () "Square")
        (F () Nothing
          (NamedType () "Digit")
          (NamedType () "SquareCell"))))

sudokuWitnessToValue :: SudokuWitness -> Value
sudokuWitnessToValue = todo
