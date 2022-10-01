{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}


module Halo2.LogicToArithmetic (eval) where


--import Halo2.Prelude
--import Halo2.FiniteField (half)
import Halo2.Types.LogicConstraint (LogicConstraint (..), AtomicLogicConstraint (..))
import Halo2.Types.LogicToArithmeticColumnLayout (LogicToArithmeticColumnLayout (..))
import Halo2.Types.Polynomial (Polynomial (..))


eval :: LogicToArithmeticColumnLayout
     -> LogicConstraint
     -> Polynomial
eval _layout =
  \case
    Atom (Equals _p _q) ->
      todo
    _ -> todo


todo :: a
todo = todo
