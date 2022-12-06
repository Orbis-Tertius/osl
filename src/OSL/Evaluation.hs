module OSL.Evaluation (evaluate) where

import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (ValidContext, Type, Term)
import OSL.Types.Value (Value)

evaluate :: ValidContext t ann -> Type ann -> Term ann -> Either (ErrorMessage ann) Value
evaluate = todo

todo :: a
todo = todo
