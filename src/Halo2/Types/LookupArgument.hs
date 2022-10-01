{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Types.LookupArgument ( LookupArgument (LookupArgument) ) where


import           Halo2.Prelude

import           Halo2.Types.InputExpression (InputExpression)
import           Halo2.Types.ColumnIndex     (ColumnIndex)


newtype LookupArgument = LookupArgument { tableMap :: [(InputExpression, ColumnIndex)] }
  deriving (Eq, Ord, Show, Generic)
