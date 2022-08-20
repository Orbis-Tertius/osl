{-# LANGUAGE DeriveGeneric #-}


module OSL.Types.OSL
  ( Name (..)
  , Type (..)
  , Term (..)
  , Bound (..)
  , LeftBound (..)
  , RightBound (..)
  , DomainBound (..)
  , CodomainBound (..)
  , ValuesBound (..)
  , LengthBound (..)
  , KeysBound (..)
  , Declaration (..)
  , Context (..)
  , ValidContext (..)
  ) where


import Data.Generics.Labels ()
import Data.Map (Map)
import Data.Text (Text, unpack)
import GHC.Generics (Generic)


data Name =
    Sym Text
  | GenSym Int
  deriving (Eq, Show, Generic)

instance Ord Name where
  Sym a <= Sym b = a <= b
  GenSym a <= GenSym b = a <= b
  Sym _ <= GenSym _ = True
  GenSym _ <= Sym _ = False


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


instance Show (Type ann) where
  show (Prop _) = "Prop"
  show (F _ a b) = "(" <> show a <> " -> " <> show b <> ")"
  show (N _) = "N"
  show (Z _) = "Z"
  show (Fin _ n) = "Fin(" <> show n <> ")"
  show (Product _ a b) = "(" <> show a <> " * " <> show b <> ")"
  show (Coproduct _ a b) = "(" <> show a <> " + " <> show b <> ")"
  show (NamedType _ (Sym a)) = unpack a
  show (NamedType _ (GenSym a)) = "$gensym" <> show a
  show (Maybe _ a) = "Maybe(" <> show a <> ")"
  show (List _ a) = "List(" <> show a <> ")"
  show (Map _ a b) = "Map(" <> show a <> ", " <> show b <> ")"


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
  | Sum ann SumLength
  | Lookup ann
  | Keys ann
  | MapPi1 ann
  | MapPi2 ann
  | MapTo ann Name
  | MapFrom ann Name
  | SumMapLength ann SumLength
  | SumListLookup ann SumLength (Term ann)
  | Equal ann (Term ann) (Term ann)
  | LessOrEqual ann (Term ann) (Term ann)
  | And ann (Term ann) (Term ann)
  | Or ann (Term ann) (Term ann)
  | Not ann (Term ann)
  | Implies ann (Term ann) (Term ann)
  | ForAll ann Name (Type ann) (Bound ann) (Term ann)
  | ForSome ann Name (Type ann) (Bound ann) (Term ann)
  deriving Show


newtype SumLength = SumLength Int
  deriving Show


data Bound ann =
    ScalarBound ann (Term ann)
  | ProductBound ann (LeftBound ann) (RightBound ann)
  | CoproductBound ann (LeftBound ann) (RightBound ann)
  | FunctionBound ann (DomainBound ann) (CodomainBound ann)
  | ListBound ann (LengthBound ann) (ValuesBound ann)
  | MaybeBound ann (ValuesBound ann)
  | MapBound ann (LengthBound ann) (KeysBound ann) (ValuesBound ann)
  | ToBound ann Name (Bound ann)
  deriving Show


newtype LeftBound ann = LeftBound { unLeftBound :: Bound ann }
  deriving Show


newtype RightBound ann = RightBound { unRightBound :: Bound ann }
  deriving Show


newtype DomainBound ann = DomainBound { unDomainBound :: Bound ann }
  deriving Show


newtype CodomainBound ann = CodomainBound { unCodomainBound :: Bound ann }
  deriving Show


newtype LengthBound ann = LengthBound { unLengthBound :: Bound ann }
  deriving Show


newtype ValuesBound ann = ValuesBound { unValuesBound :: Bound ann }
  deriving Show


newtype KeysBound ann = KeysBound { unKeysBound :: Bound ann }
  deriving Show


data Declaration ann =
    FreeVariable (Type ann)
  | Data (Type ann)
  | Defined (Type ann) (Term ann)


newtype Context ann = Context { unContext :: [(Name, Declaration ann)] }


newtype ValidContext ann =
  ValidContext { unValidContext :: Map Name (Declaration ann) }
