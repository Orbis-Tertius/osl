{-# LANGUAGE OverloadedStrings #-}

module OSL.Witness (preprocessWitness) where

import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import OSL.Term (termAnnotation)
import OSL.Types.Argument (Witness (Witness))
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Types.EvaluationContext (EvaluationContext)
import OSL.Types.OSL (Term)
import OSL.Types.PreprocessedWitness (PreprocessedWitness (PreprocessedWitness))

preprocessWitness :: Ord ann => Term ann -> Witness -> Either (ErrorMessage ann) (PreprocessedWitness ann)
preprocessWitness x0 w0 =
  pure $ PreprocessedWitness (go x0 w0)
  where
    go x (Witness w) ann e =
      if termAnnotation x == ann
      then pure w
      else -- traverse term and witness
        case Map.lookup ann telescopes of
          Nothing -> Left . ErrorMessage ann $ "telescope not found (this is a compiler bug)"
          Just (Telescope []) ->
            Left . ErrorMessage ann $ "empty telescope (this is a compiler bug)"
          Just (Telescope [_]) ->
            Left . ErrorMessage ann $ "premature end of telescope (this is a compiler bug)"
          Just (Telescope (t0:t1:ts)) ->
            if t0 == x
            then do
              branches <- getDirectSubformulasAndPairedWitnesses x (Witness w) e
              case find ((== termAnnotation t1) . termAnnotation . fst) branches of
                Just (u, v) -> todo u v
                Nothing -> Left . ErrorMessage ann $
                  "telescope traversal failed (this is a compiler bug)"
            else todo
    telescopes = getSubformulaTelescopes x0

-- The telescope of a subterm is the sequence of its enclosing subterms, beginning with
-- the overall term and ending with the subterm itself. Having the telescope
-- of a subterm helps with traversing the overall formula and concurrently traversing
-- the witness in order to find the piece of the witness that is relevant to the
-- given annotation and the evaluation context.
newtype Telescope ann = Telescope [Term ann]

-- Get the map of subformula annotations to their telescopes.
getSubformulaTelescopes :: Ord ann => Term ann -> Map ann (Telescope ann)
getSubformulaTelescopes = todo

getDirectSubformulas :: Term ann -> [Term ann]
getDirectSubformulas = todo

getDirectSubformulasAndPairedWitnesses :: Term ann -> Witness -> EvaluationContext -> Either (ErrorMessage ann) [(Term ann, Witness)]
getDirectSubformulasAndPairedWitnesses = todo

todo :: a
todo = todo
