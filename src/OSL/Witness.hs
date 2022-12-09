module OSL.Witness (preprocessWitness) where

import OSL.Types.Argument (Witness)
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (Term)
import OSL.Types.PreprocessedWitness (PreprocessedWitness)

preprocessWitness :: Term ann -> Witness -> Either (ErrorMessage ann) (PreprocessedWitness ann)
preprocessWitness = todo

todo :: a
todo = todo
