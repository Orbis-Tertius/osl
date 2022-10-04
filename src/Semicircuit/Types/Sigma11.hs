-- This is different from OSL.Types.Sigma11
-- in that the types in this module use explicit
-- variable names rather than de Bruijn indices.
-- This is more convenient for conversion to
-- prenex normal forms.
--
-- You might ask, why not just let the types in
-- OSL.Types.Sigma11 be parameterized by the
-- type of names? The reason is that in
-- OSL.Types.Sigma11, the variable names are implied
-- in quantifiers, whereas in this module, the
-- variable names are given explicitly in quantifiers.

module Semicircuit.Types.Sigma11
  ( Name (Name)
  , Term (..)
  , Formula (..)
  , ExistentialQuantifier (..)
  , Bound (..)
  ) where



