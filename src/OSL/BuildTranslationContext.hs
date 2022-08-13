module OSL.BuildTranslationContext
  ( buildTranslationContext
  ) where


import Control.Monad (forM_)

import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (ValidContext)
import OSL.ValidContext (getDeclaration)


-- builds a translation context providing mappings
-- for all of the free variables in the given context.
buildTranslationContext
  :: ValidContext ann
  -> Either ErrorMessage TranslationContext
buildTranslationContext c =
  let freeVariables = getFreeVariables c
  in (execStateT
       (runExceptT
         (forM_
           freeVariables
           (addFreeVariableMapping c)))
       (TranslationContext mempty))


addFreeVariableMapping
  :: Monad m
  => ValidContext ann
  -> TranslationContext
  -> OSL.Name
  -> StateT TranslationContext (ExceptT ErrorMessage m) ()
addFreeVariableMapping c t freeVariable =
  let decl = getExistingDeclaration c freeVariable in
  case decl of
    FreeVariable t ->
      case t of
        Prop _ -> Left (ErrorMessage "free Prop variable")
        N _ -> ScalarMapping <$> getFreeS11Name 
    _ -> die "logically impossible: free variable is not a free variable"


getFreeVariables :: ValidContext ann -> [OSL.Name]
getFreeVariables c@(ValidContext decls) =
  Map.keys (Map.filter isFree decls)
  where
    isFree (FreeVariable _) = True
    isFree _ = False


todo :: a
todo = todo
