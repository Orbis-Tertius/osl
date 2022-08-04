module OSL.Types.OSL
  ( Name (..)
  , Type (..)
  , Term (..)
  , Declaration (..)
  , Context (..)
  , ValidContext (..)
  ) where


import Data.Map (Map)
import Data.Text (Text)


newtype Name = Name { unName :: Text }
  deriving (Eq, Ord, Show)


data Type ann =
    Prop ann
  | F ann (Type ann) (Type ann) -- functions
  | N ann -- natural numbers
  | Z ann -- integers
  | Fin ann Integer
  | Product ann (Type ann) (Type ann)
  | Coproduct ann (Type ann) (Type ann)
  | NamedType ann Name
  | Maybe ann (Type ann)
  | List ann (Type ann)
  | Map ann (Type ann) (Type ann)
  deriving Show


data Term ann =
    NamedTerm ann Name
  | AddN ann
  | MulN ann
  | ConstN ann Integer
  | AddZ ann
  | MulZ ann
  | ConstZ ann Integer
  | Cast ann
  | ConstFin ann Integer
  | Pair ann
  | Pi1 ann -- Product projections
  | Pi2 ann
  | Iota1 ann -- Coproduct injections
  | Iota2 ann
  | FunctionProduct ann (Term ann) (Term ann)
  | FunctionCoproduct ann (Term ann) (Term ann)
  | Lambda ann Name (Type ann) (Term ann)
  | Apply ann (Term ann) (Term ann)
  | To ann Name
  | From ann Name
  | Let ann Name (Type ann) (Term ann) (Term ann)
  | Just' ann
  | Nothing' ann
  | Maybe' ann (Term ann)
  | Exists ann
  | Length ann
  | Nth ann
  | ListPi1 ann
  | ListPi2 ann
  | ListTo ann Name
  | ListFrom ann Name
  | ListLength ann
  | ListMaybePi1 ann
  | ListMaybePi2 ann
  | ListMaybeLength ann
  | Sum ann
  | Lookup ann
  | Keys ann
  | MapPi1 ann
  | MapPi2 ann
  | MapTo ann Name
  | MapFrom ann Name
  | SumMapLength ann
  | SumListLookup ann (Term ann)
  | Equal ann (Term ann) (Term ann)
  | LessOrEqual ann (Term ann) (Term ann)
  | And ann (Term ann) (Term ann)
  | Or ann (Term ann) (Term ann)
  | Not ann (Term ann)
  | Implies ann (Term ann) (Term ann)
  | ForAll ann Name (Type ann) (Term ann)
  | ForSome ann Name (Type ann) (Term ann)
  deriving Show


data Declaration ann =
    FreeVariable (Type ann)
  | Data (Type ann)
  | Defined (Type ann) (Term ann)


newtype Context ann = Context { unContext :: [(Name, Declaration ann)] }


newtype ValidContext ann =
  ValidContext { unValidContext :: Map Name (Declaration ann) }
