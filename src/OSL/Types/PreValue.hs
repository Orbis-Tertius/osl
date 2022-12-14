module OSL.Types.PreValue (PreValue (Value, LambdaClosure, PrePair, PreTo, PreIota1, PreIota2)) where

import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (Name)
import OSL.Types.Value (Value)

data PreValue ann =
    Value Value
  | LambdaClosure (PreValue ann -> Either (ErrorMessage ann) (PreValue ann))
  | PrePair (PreValue ann) (PreValue ann)
  | PreTo Name (PreValue ann)
  | PreIota1 (PreValue ann)
  | PreIota2 (PreValue ann)
