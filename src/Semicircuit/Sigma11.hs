module Semicircuit.Sigma11
  ( prependBounds
  ) where


import Semicircuit.Types.Sigma11 (ExistentialQuantifier (Some, SomeP), InputBound (..))


prependBounds
  :: [InputBound]
  -> ExistentialQuantifier
  -> ExistentialQuantifier
prependBounds bs' (Some x n bs b) =
  Some x n (bs' <> bs) b
prependBounds _ (SomeP _ _ _ _) =
  error "there is a compiler bug; applied prependBounds to SomeP"
