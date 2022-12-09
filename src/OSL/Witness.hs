module OSL.Witness (preprocessWitness) where

import Data.Map (Map)
import OSL.Types.Argument (Witness)
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (Term)
import OSL.Types.PreprocessedWitness (PreprocessedWitness)

preprocessWitness :: Term ann -> Witness -> Either (ErrorMessage ann) (PreprocessedWitness ann)
preprocessWitness = todo

-- The telescope of a subterm is the sequence of its enclosing subterms, beginning with
-- the overall term and ending with the subterm itself. Having the telescope
-- of a subterm helps with traversing the overall formula and concurrently traversing
-- the witness in order to find the piece of the witness that it is relevant
-- to the given annotation and the evaluation context.
newtype Telescope ann = Telescope [Term ann]

-- Get the map of subformula annotations to their telescopes.
getSubformulaTelescopes :: Ord ann => Term ann -> Map ann (Telescope ann)
getSubformulaTelescopes = todo

todo :: a
todo = todo
