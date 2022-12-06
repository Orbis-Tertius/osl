{-# LANGUAGE DataKinds #-}

module OSL.Satisfaction (satisfies) where

import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.Argument (Argument)
import OSL.Types.OSL (Type, Term, ValidContext, ContextType (Global))

satisfies :: ValidContext 'Global ann -> Type ann -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfies = todo

todo :: a
todo = todo
