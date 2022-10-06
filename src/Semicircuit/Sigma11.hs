module Semicircuit.Sigma11
  ( prependBounds
  , prependQuantifiers
  ) where


import Semicircuit.Types.Sigma11 (ExistentialQuantifier (Some, SomeP), InputBound (..), Quantifier (Universal, Existential), Formula (ForAll, ForSome))


prependBounds
  :: [InputBound]
  -> ExistentialQuantifier
  -> ExistentialQuantifier
prependBounds bs' (Some x n bs b) =
  Some x n (bs' <> bs) b
prependBounds _ (SomeP _ _ _ _) =
  error "there is a compiler bug; applied prependBounds to SomeP"


prependQuantifiers :: [Quantifier] -> Formula -> Formula
prependQuantifiers qs f =
  foldl (flip prependQuantifier) f qs


prependQuantifier :: Quantifier -> Formula -> Formula
prependQuantifier (Universal x b) f =
  ForAll x b f
prependQuantifier (Existential q) f =
  ForSome q f
