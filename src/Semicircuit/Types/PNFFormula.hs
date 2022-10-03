module Semicircuit.Types.PNFFormula
  ( PNFFormula (..)
  ) where


data PNFFormula =
  PNFFormula
  { qfFormula :: QFFormula
  , foQuantifiers :: FOQuantifiers
  , soQuantifiers :: SOQuantifiers
  }


data PNFFormula' =
  PNFFormula'
  { qfFormula :: QFFormula
  , quantifiers :: Quantifiers
  }


data Quantifiers =
  Quantifiers
  { foExistentialQuantifiers :: [FOExistentialQuantifier]
  , foUniversalQuantifiers :: [FOUniversalQuantifier]
  , soQuantifiers :: SOQuantifiers
  }


data FOExistentialQuantifier =
  FOExistentialQuantifier
  Bound
  NumberOfPrecedingUniversalQuantifiers


newtype NumberOfPrecedingUniversalQuantifiers =
  NumberOfPrecedingUniversalQuantifiers Int


data FOUniversalQuantifier =
  FOUniversalQuantifier Bound


newtype FOQuantifiers = FOQuantifiers [FOQuantifier]


newtype SOQuantifiers = SOQuantifiers [SOQuantifier]


data FOQuantifier =
    ForAll Bound
  | ExistsFO Bound


data SOQuantifier =
    SOQuantifier Cardinality Bound (NonEmpty Bound)
  | SOPQuantifier Cardinality Bound Bound
