{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Halo2.Types.InputExpression (InputExpression (InputExpression, getInputExpression)) where

import Halo2.Prelude

newtype InputExpression a = InputExpression {getInputExpression :: a}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (Show)
