{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module OSL.Format (formatContext) where

import Control.Lens ((^.))
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (pack)
import Die (die)
import OSL.Types.OSL (Declaration (Data, Defined, FreeVariable), Name, ValidContext)

formatContext :: ValidContext t ann -> [Name] -> String
formatContext c nms =
  intercalate
    "\n"
    ( uncurry formatDeclaration
        <$> [ (nm, decl)
              | nm <- nms,
                let decl =
                      fromMaybe
                        (die $ "formatContext: undefined name: " <> pack (show nm))
                        (Map.lookup nm (c ^. #unValidContext))
            ]
    )

formatDeclaration :: Name -> Declaration ann -> String
formatDeclaration nm =
  \case
    Data a -> "data " <> show nm <> " ≅ " <> show a <> "."
    FreeVariable a -> show nm <> " : " <> show a <> "."
    Defined {} -> die "formatContext: unsupported: defined terms"
