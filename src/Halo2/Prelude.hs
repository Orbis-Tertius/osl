{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.Prelude
  ( module Prelude
  , module Control.Lens
  , module Data.Map
  , module Data.Set
  , module GHC.Generics
  ) where


import Control.Lens ((^.))
import           Data.Map     (Map)
import           Data.Set     (Set)
import Data.Generics.Labels ()
import           GHC.Generics (Generic)
import           Prelude
