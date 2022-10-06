module Semicircuit.Sigma11
  ( prependBounds
  ) where


import OSL.Types.Cardinality (Cardinality)
import Semicircuit.Types.Sigma11 (ExistentialQuantifier (Some, SomeP), InputBound (..))


prependBounds
  :: Cardinality
  -> [InputBound]
  -> ExistentialQuantifier
  -> ExistentialQuantifier
prependBounds _ bs' (Some x n bs b) =
  Some x n (bs' <> bs) b
prependBounds _ _ (SomeP _ _ _ _) =
  error "there is a compiler bug; applied prependBounds to SomeP"
