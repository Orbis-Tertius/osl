module Trace.Semantics
  ( evalTrace
  ) where

import OSL.Types.ErrorMessage (ErrorMessage)
import Trace.Types (TraceType, Trace)

evalTrace ::
  ann ->
  TraceType ->
  Trace ->
  Either (ErrorMessage ann) Bool
evalTrace = todo

todo :: a
todo = todo
