{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.InputExpression (InputExpression (InputExpression, getInputExpression)) where

import Halo2.Prelude
import Halo2.Types.Polynomial (Polynomial)

newtype InputExpression = InputExpression {getInputExpression :: Polynomial}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)
