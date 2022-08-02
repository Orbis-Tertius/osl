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


data Type =
    Prop
  | Function Type Type
  | N -- natural numbers
  | Z -- integers
  | Fin Integer
  | Product Type Type
  | Coproduct Type Type
  | NamedType Name
  | Maybe Type
  | List Type
  | Map Type Type


data Term =
    NamedTerm Name
  | AddN
  | MulN
  | ConstN Integer
  | AddZ
  | MulZ
  | ConstZ Integer
  | Cast
  | ConstFin Integer
  | Cons Term Term
  | Pi1 Term -- Product projections
  | Pi2 Term
  | Iota1 Term -- Coproduct injections
  | Iota2 Term
  | FunctionProduct Term Term
  | FunctionCoproduct Term Term
  | Lambda Name Type Term
  | Apply Term Term
  | To Name
  | From Name
  | Let Name Type Term Term
  | Just'
  | Nothing'
  | Maybe'
  | Exists
  | Length
  | Nth
  | ListPi1
  | ListPi2
  | ListTo Name
  | ListFrom Name
  | ListLength
  | ListMaybePi1
  | ListMaybePi2
  | ListMaybeLength
  | Sum
  | Lookup
  | Keys
  | MapPi1
  | MapPi2
  | MapTo Name
  | MapFrom Name
  | SumMapLength
  | SumListLookup Term


data Declaration =
    FreeVariable Type
  | Data Type
  | Defined Type Term


newtype Context = Context { unContext :: [Declaration] }


newtype ValidContext = ValidContext { unValidContext :: Map Name Declaration }
