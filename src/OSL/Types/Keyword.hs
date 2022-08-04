module OSL.Types.Keyword (Keyword (..)) where


data Keyword = Type | Prop | N | Z | Fin | Cast | Data | To | From | Def
  | Maybe | Maybe' | Just' | Nothing' | Exists | List | Length | Nth | Sum | Let
  | Pi1 | Pi2 | Iota1 | Iota2 | Map | Lookup | Keys | SumMapLength | SumListLookup
  deriving (Eq, Show)
