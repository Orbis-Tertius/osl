{-# LANGUAGE DataKinds #-}

module OSL.Satisfaction (satisfies) where

import OSL.Types.Argument (Argument)
import OSL.Types.ErrorMessage (ErrorMessage)
import OSL.Types.OSL (ContextType (Global), Term, Type, ValidContext)

satisfies :: ValidContext 'Global ann -> Type ann -> Term ann -> Argument -> Either (ErrorMessage ann) Bool
satisfies = todo

todo :: a
todo = todo
