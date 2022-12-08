{-# LANGUAGE LambdaCase #-}

module OSL.Types.Value
  ( Value (Nat, Int, Fin', Fp', Pair', Iota1', Iota2', To', Maybe'', List'', Map'', Fun, Bool, Predicate)
  ) where

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import OSL.Types.OSL (Name)
import Stark.Types.Scalar (Scalar)

data Value
  = Nat Scalar
  | Int Scalar
  | Fp' Scalar
  | Fin' Scalar
  | Pair' Value Value
  | Iota1' Value
  | Iota2' Value
  | To' Name Value
  | Maybe'' (Maybe Value)
  | List'' [Value]
  | Map'' (Map Value Value)
  | Fun (Map Value Value)
  | Bool Bool
  | Predicate (Set Value)
  deriving (Eq, Ord)

instance Show Value where
  show =
    \case
      Nat x -> show x <> "N"
      Int x -> show x <> "Z"
      Fin' x -> "fin(" <> show x <> ")"
      Fp' x -> show x <> "F"
      Pair' x y -> "(" <> show x <> ", " <> show y <> ")"
      Iota1' x -> "iota1(" <> show x <> ")"
      Iota2' x -> "iota2(" <> show x <> ")"
      To' t x -> "to(" <> show t <> ", " <> show x <> ")"
      Maybe'' (Just x) -> "just(" <> show x <> ")"
      Maybe'' Nothing -> "nothing"
      List'' xs -> "[" <> intercalate ", " (show <$> xs) <> "]"
      Map'' xs -> "map(" <> intercalate ", " (show <$> Map.toList xs) <> ")"
      Fun xs -> "fun(" <> intercalate ", " (show <$> Map.toList xs) <> ")"
      Bool x -> show x
      Predicate p -> "pred(" <> intercalate ", " (show <$> Set.toList p) <> ")"
