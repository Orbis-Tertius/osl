{-# LANGUAGE DeriveGeneric #-}


module OSL.Types.Sigma11
  ( Name (Name)
  , Term (..)
  , Formula (..)
  , ExistentialQuantifier (..)
  ) where


import Data.List.NonEmpty (NonEmpty)
import Data.Generics.Labels ()
import GHC.Generics (Generic)

import OSL.Types.Arity (Arity)
import OSL.Types.DeBruijnIndex (DeBruijnIndex)


data Name = Name { arity :: Arity, deBruijnIndex :: DeBruijnIndex }
  deriving (Eq, Ord, Generic)


data Term =
    Var Name
  | App Name (NonEmpty Term)
  | Add Term Term
  | Mul Term Term
  | IndLess Term Term
  | Const Integer


data Formula =
    Equal Term Term
  | LessOrEqual Term Term
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | ForAll Term Formula
  | Exists ExistentialQuantifier Formula


data ExistentialQuantifier =
    ExistsFO Term
  | ExistsSO Term (NonEmpty Term)
