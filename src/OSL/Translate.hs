{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.Translate
  ( translate
  , translateToTerm
  , translateToFormula
  ) where


import Control.Applicative (liftA2)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.State.Strict (execStateT)
import Data.Functor.Identity (runIdentity)
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Text (pack)

import OSL.BuildTranslationContext (buildTranslationContext', getFreeOSLName, addFreeVariableMapping, addTermMapping)
import OSL.Die (die)
import OSL.Sigma11 (incrementDeBruijnIndices, incrementArities, prependBounds)
import OSL.Term (termAnnotation, boundAnnotation)
import OSL.TranslationContext (mergeMappings, mergeMapping)
import OSL.Type (typeAnnotation)
import OSL.Types.Arity (Arity (..))
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.Translation (Translation (Formula, Term, Mapping))
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..), LeftMapping (..), RightMapping (..), ChoiceMapping (..), ValuesMapping (..), MappingDimensions (..), LengthMapping (..), KeyIndicatorMapping (..), KeysMapping (..))
import OSL.ValidContext (getDeclaration, addDeclaration)
import OSL.ValidateContext (inferType)


-- Provides a translation for the given term in
-- the given context.
translate
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) (Translation ann)
translate ctx@(TranslationContext
          decls@(OSL.ValidContext declsMap) mappings)
          termType =
  \case
    OSL.NamedTerm ann name ->
      case Map.lookup name mappings of
        Just (ScalarMapping x) -> return (Term x)
        Just m -> return (Mapping m)
        Nothing -> Left (ErrorMessage ann "un-mapped name")
    OSL.Apply ann (OSL.Apply _ (OSL.AddN _) a) b ->
      Term <$> (S11.Add <$> translateToTerm ctx (OSL.N ann) a
                        <*> translateToTerm ctx (OSL.N ann) b)
    OSL.Apply ann (OSL.Apply _ (OSL.MulN _) a) b ->
      Term <$> (S11.Mul <$> translateToTerm ctx (OSL.N ann) a
                        <*> translateToTerm ctx (OSL.N ann) b)
    OSL.Apply ann (OSL.Apply _ (OSL.AddZ _) a) b ->
      Term <$> (S11.Add <$> translateToTerm ctx (OSL.Z ann) a
                        <*> translateToTerm ctx (OSL.Z ann) b)
    OSL.Apply ann (OSL.Apply _ (OSL.MulZ _) a) b ->
      Term <$> (S11.Mul <$> translateToTerm ctx (OSL.Z ann) a
                        <*> translateToTerm ctx (OSL.Z ann) b)
    OSL.Apply _ (OSL.Cast _) a -> do
      aT <- inferType decls a
      translate ctx aT a
    OSL.ConstN _ x -> return (Term (S11.Const x))
    OSL.ConstZ _ x -> return (Term (S11.Const x))
    OSL.ConstFin _ x -> return (Term (S11.Const x))
    OSL.Apply ann (OSL.NamedTerm ann' fName) x ->
      case getDeclaration decls fName of
        Just (OSL.Defined _ f) -> translate ctx termType (OSL.Apply ann f x)
        Just _ -> Left (ErrorMessage ann' "expected the name of a defined function")
        Nothing -> Left (ErrorMessage ann' "undefined name")
    OSL.Apply ann (OSL.Apply _ (OSL.Pair _) a) b ->
      case termType of
        OSL.Product _ aType bType -> do
          Mapping <$>
            (ProductMapping
              <$> (LeftMapping <$> translateToMapping ctx aType a)
              <*> (RightMapping <$> translateToMapping ctx bType b))
        _ -> Left (ErrorMessage ann $
          "expected a " <> pack (show termType))
    OSL.Apply ann (OSL.Pi1 _) a -> do
      aT <- inferType decls a
      aM <- translateToMapping ctx aT a
      case aM of
        ProductMapping (LeftMapping m) _ ->
          return (Mapping m)
        _ -> Left (ErrorMessage ann "expected a pair")
    OSL.Apply ann (OSL.Pi2 _) a -> do
      aT <- inferType decls a
      aM <- translateToMapping ctx aT a
      case aM of
        ProductMapping _ (RightMapping m) ->
          return (Mapping m)
        _ -> Left (ErrorMessage ann "expected a pair")
    OSL.Apply ann (OSL.Iota1 _) a ->
      case termType of
        OSL.Coproduct _ b c -> do
          aM <- translateToMapping ctx b a
          bM <- getArbitraryMapping decls c
          return . Mapping
            $ CoproductMapping
              (ChoiceMapping (ScalarMapping (S11.Const 0)))
              (LeftMapping aM)
              (RightMapping bM)
        _ -> Left (ErrorMessage ann "expected a coproduct")
    OSL.Apply ann (OSL.Iota2 _) a ->
      case termType of
        OSL.Coproduct _ b c -> do
          aM <- getArbitraryMapping decls b
          bM <- translateToMapping ctx c a
          return . Mapping
            $ CoproductMapping
              (ChoiceMapping (ScalarMapping (S11.Const 0)))
              (LeftMapping aM)
              (RightMapping bM)
        _ -> Left (ErrorMessage ann "expected a coproduct")
    OSL.FunctionProduct ann f g ->
      case termType of
        OSL.F ann' n a (OSL.Product _ b c) ->
          Mapping
          <$> (ProductMapping
            <$> (LeftMapping <$> translateToMapping ctx (OSL.F ann' n a b) f)
            <*> (RightMapping <$> translateToMapping ctx (OSL.F ann' n a c) g))
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show termType)
    OSL.FunctionCoproduct ann f g ->
      case termType of
        OSL.F ann' n a (OSL.Coproduct _ b c) ->
          Mapping
          <$> (FunctionCoproductMapping
            <$> (LeftMapping <$> translateToMapping ctx (OSL.F ann' n a b) f)
            <*> (RightMapping <$> translateToMapping ctx (OSL.F ann' n a c) g))
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show termType)
    OSL.Lambda _ v vT t ->
      pure (Mapping (LambdaMapping ctx v vT t))
    OSL.Apply _ (OSL.Lambda _ varName varType body) x -> do
      xM <- translateToMapping ctx varType x
      let decls' = OSL.ValidContext
                     (Map.insert varName (OSL.Defined varType x) declsMap)
          ctx' = TranslationContext decls' (Map.insert varName xM mappings)
      translate ctx' termType body
    OSL.Apply _ (OSL.To ann typeName) x ->
      case getDeclaration decls typeName of
        Just (OSL.Data typeDef) -> translate ctx typeDef x
        Just _ -> Left (ErrorMessage ann "expected the name of a type")
        Nothing -> Left (ErrorMessage ann "undefined name")
    OSL.Apply _ (OSL.From ann typeName) x ->
      translate ctx (OSL.NamedType ann typeName) x
    OSL.Apply ann (OSL.Just' _) x ->
      case termType of
        OSL.Maybe _ xType ->
          Mapping . MaybeMapping (ChoiceMapping (ScalarMapping (S11.Const 1)))
            . ValuesMapping <$> translateToMapping ctx xType x
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show termType)
    OSL.Nothing' ann ->
      case termType of
        OSL.Maybe _ xType ->
          Mapping . MaybeMapping (ChoiceMapping (ScalarMapping (S11.Const 0)))
            . ValuesMapping <$> getArbitraryMapping decls xType
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show termType)
    OSL.Apply ann (OSL.Apply _ (OSL.Maybe' ann' f) b) a -> do
      fType <- inferType decls f
      case fType of
        OSL.F _ _ aType _ -> do
          aM <- translateToMapping ctx (OSL.Maybe ann aType) a
          bT <- translateToTerm ctx termType b
          fM <- translateToMapping ctx fType f
          case aM of
            MaybeMapping (ChoiceMapping (ScalarMapping choiceT))
                         (ValuesMapping vM) -> do
              fvM <- applyMappings ann ctx fM vM
              case fvM of
                ScalarMapping fvT ->
                  pure . Term $ (choiceT `S11.Mul` fvT)
                    `S11.Add`
                     ((S11.Const 1 `S11.Add`
                       (S11.Const (-1) `S11.Mul` choiceT))
                      `S11.Mul` bT)
                _ -> Left . ErrorMessage ann $ "expected a scalar value"
            _ -> Left . ErrorMessage ann $ "expected a maybe value"
        _ -> Left . ErrorMessage ann' $ "expected a function"
    OSL.Apply ann (OSL.Exists _) mx -> do
      mxM <- translateToMapping ctx (OSL.Maybe ann termType) mx
      case mxM of
        MaybeMapping _ (ValuesMapping xM) -> pure (Mapping xM)
        _ -> Left . ErrorMessage ann $ "expected a maybe mapping"
    OSL.Apply ann (OSL.Length _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping (LengthMapping (ScalarMapping lT)) _ -> pure (Term lT)
        _ -> Left (ErrorMessage ann "expected a list")
    OSL.Apply ann (OSL.Apply _ (OSL.Nth _) xs) i -> do
      iT <- translateToTerm ctx (OSL.N ann) i
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      Mapping <$> applyMappings ann ctx xsM (const iT <$> xsM)
    OSL.Apply ann (OSL.ListPi1 _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping lM (ValuesMapping (ProductMapping (LeftMapping aM) _)) ->
          pure . Mapping $ ListMapping lM (ValuesMapping aM)
        _ -> Left . ErrorMessage ann $ "expected a list of pairs"
    OSL.Apply ann (OSL.ListPi2 _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping lM (ValuesMapping (ProductMapping _ (RightMapping bM))) ->
          pure . Mapping $ ListMapping lM (ValuesMapping bM)
        _ -> Left . ErrorMessage ann $ "expected a list of pairs"
    OSL.Apply ann (OSL.ListTo ann' name) xs -> do
      case getDeclaration decls name of
        Just (OSL.Data a) -> do
          xsType <- inferType decls xs
          case xsType of
            OSL.List _ n _ ->
              Mapping <$> translateToMapping ctx (OSL.List ann' n a) xs
            _ -> Left (ErrorMessage ann "expected a list")
        Just _ -> Left (ErrorMessage ann' "expected the name of a type")
        Nothing -> Left (ErrorMessage ann' "undefined name")
    OSL.Apply ann (OSL.ListFrom ann' name) xs ->
      case getDeclaration decls name of
        Just (OSL.Data a) -> do
          xsType <- inferType decls xs
          case xsType of
            OSL.List _ n _ ->
              Mapping <$> translateToMapping ctx (OSL.List ann' n a) xs
            _ -> Left (ErrorMessage ann "expected a list")
        Just _ -> Left (ErrorMessage ann' "expected the name of a type")
        Nothing -> Left (ErrorMessage ann' "undefined name")
    OSL.Apply ann (OSL.ListLength _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping lM (ValuesMapping (ListMapping (LengthMapping xslM) _)) ->
          pure . Mapping $ ListMapping lM (ValuesMapping xslM)
        _ -> Left (ErrorMessage ann "expected a list of lists")
    OSL.Apply ann (OSL.ListMaybePi1 _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping lM
          (ValuesMapping
            (MaybeMapping cM
              (ValuesMapping
                (ProductMapping (LeftMapping aM) (RightMapping _))))) -> do
          pure . Mapping
            $ ListMapping lM
              (ValuesMapping
                (MaybeMapping cM (ValuesMapping aM)))
        _ -> Left (ErrorMessage ann "expected a list of maybe pair")
    OSL.Apply ann (OSL.ListMaybePi2 _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping lM
          (ValuesMapping
            (MaybeMapping cM
              (ValuesMapping
                (ProductMapping (LeftMapping _) (RightMapping bM))))) -> do
          pure . Mapping
            $ ListMapping lM
              (ValuesMapping
                (MaybeMapping cM (ValuesMapping bM)))
        _ -> Left (ErrorMessage ann "expected a list of maybe pair")
    OSL.Apply ann (OSL.ListMaybeLength _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsM of
        ListMapping lM
          (ValuesMapping
            (MaybeMapping cM
              (ValuesMapping (ListMapping (LengthMapping xslM) _)))) ->
          pure . Mapping
            $ ListMapping lM
              (ValuesMapping (MaybeMapping cM (ValuesMapping xslM)))
        _ -> Left (ErrorMessage ann "expected a list of maybe list")
    OSL.Apply ann (OSL.Sum _) xs -> do
      xsType <- inferType decls xs
      xsM <- translateToMapping ctx xsType xs
      case xsType of
        OSL.List _ (OSL.Cardinality n) (OSL.List _ (OSL.Cardinality m) _) ->
          case xsM of
            ListMapping (LengthMapping (ScalarMapping lT))
              (ValuesMapping
                (ListMapping (LengthMapping (ScalarMapping rT))
                  (ValuesMapping
                    (MaybeMapping
                      (ChoiceMapping (ScalarMapping cT))
                      (ValuesMapping (ScalarMapping vT)))))) ->
              Term <$>
              foldl (liftA2 (S11.Add)) (pure (S11.Const 0))
              [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
              . (S11.IndLess (S11.Const j) rT `S11.Mul`)
               <$> (S11.Mul
                 <$> (flip (applyTerms ann) (S11.Const j)
                        =<< applyTerms ann vT (S11.Const i))
                 <*> (flip (applyTerms ann) (S11.Const j)
                        =<< applyTerms ann cT (S11.Const i)))
              | i <- [0..n-1], j <- [0..m-1] ]
            ListMapping (LengthMapping (ScalarMapping lT))
              (ValuesMapping
                (ListMapping (LengthMapping (ScalarMapping rT))
                  (ValuesMapping
                    (ScalarMapping vT)))) ->
              Term <$>
              foldl (liftA2 (S11.Add)) (pure (S11.Const 0))
              [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
              . (S11.IndLess (S11.Const j) rT `S11.Mul`)
                <$> (flip (applyTerms ann) (S11.Const j)
                     =<< applyTerms ann vT (S11.Const i))
              | i <- [0..n-1], j <- [0..m-1] ]
            _ -> Left (ErrorMessage ann "expected a list mapping")
        OSL.List _ (OSL.Cardinality n) _ ->
          case xsM of
            ListMapping (LengthMapping (ScalarMapping lT))
              (ValuesMapping
                (MaybeMapping (ChoiceMapping (ScalarMapping cT))
                  (ValuesMapping (ScalarMapping vT)))) ->
              Term <$>
              foldl (liftA2 (S11.Add)) (pure (S11.Const 0))
                [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                  <$> (S11.Mul <$> applyTerms ann cT (S11.Const i)
                               <*> applyTerms ann vT (S11.Const i))
                | i <- [0..n-1] ]
            ListMapping (LengthMapping (ScalarMapping lT))
                        (ValuesMapping (ScalarMapping xsT)) ->
              Term <$>
              foldl (liftA2 (S11.Add)) (pure (S11.Const 0))
                [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                   <$> applyTerms ann xsT (S11.Const i)
                | i <- [0..n-1] ]
            _ -> Left (ErrorMessage ann "expected a list mapping")
        OSL.Map _ (OSL.Cardinality n) _ _ ->
          case xsM of
            MapMapping (LengthMapping (ScalarMapping lT))
                       (KeysMapping (ScalarMapping kT))
                       _
                       (ValuesMapping (ScalarMapping vT)) ->
              Term <$>
              foldl (liftA2 (S11.Add)) (pure (S11.Const 0))
                [ (S11.IndLess (S11.Const i) lT `S11.Mul`)
                  <$> (applyTerms ann vT =<< applyTerms ann kT (S11.Const i))
                | i <- [0..n-1] ]
            _ -> Left (ErrorMessage ann "expected a map mapping")
        _ -> Left (ErrorMessage ann "expected a list or map type")
    OSL.Apply ann (OSL.Apply _ (OSL.Lookup _) k) xs -> do
      xsType <- inferType decls xs
      case xsType of
        OSL.Map _ _ kType _ -> do
          xsM <- translateToMapping ctx xsType xs
          kM <- translateToMapping ctx kType k
          case xsM of
            MapMapping _ _ (KeyIndicatorMapping indM)
                (ValuesMapping vM) -> do
              kExistsM <- applyMappings ann ctx indM kM
              vM' <- applyMappings ann ctx vM kM
              pure . Mapping
                $ MaybeMapping (ChoiceMapping kExistsM) (ValuesMapping vM')
            _ -> Left (ErrorMessage ann "expected a map mapping")
        _ -> Left (ErrorMessage ann "expected a map")
    OSL.Apply ann (OSL.MapPi1 _) xs -> do
      xsType <- inferType decls xs
      case xsType of
        OSL.Map _ _ _ (OSL.Product _ _ _) -> do
          xsM <- translateToMapping ctx xsType xs
          case xsM of
            MapMapping lM kM iM (ValuesMapping
                (ProductMapping (LeftMapping aM) _)) ->
              pure . Mapping $ MapMapping lM kM iM (ValuesMapping aM)
            _ -> Left (ErrorMessage ann "expected a map mapping")
        _ -> Left (ErrorMessage ann "expected a map")
    OSL.Apply ann (OSL.MapPi2 _) xs -> do
      xsType <- inferType decls xs
      case xsType of
        OSL.Map _ _ _ (OSL.Product _ _ _) -> do
          xsM <- translateToMapping ctx xsType xs
          case xsM of
            MapMapping lM kM iM (ValuesMapping
                (ProductMapping _ (RightMapping bM))) ->
              pure . Mapping $ MapMapping lM kM iM (ValuesMapping bM)
            _ -> Left (ErrorMessage ann "expected a map mapping")
        _ -> Left (ErrorMessage ann "expected a map")
    OSL.Apply _ (OSL.MapTo _ _) xs -> do
      xsType <- inferType decls xs
      translate ctx xsType xs
    OSL.Apply _ (OSL.MapFrom _ _) xs -> do
      xsType <- inferType decls xs
      translate ctx xsType xs
    OSL.Apply ann (OSL.Keys _) xs -> do
      xsType <- inferType decls xs
      case xsType of
        OSL.Map _ _ _ _ -> do
          xsM <- translateToMapping ctx xsType xs
          case xsM of
            MapMapping lM (KeysMapping kM) _ _ ->
              pure . Mapping $ ListMapping lM (ValuesMapping kM)
            _ -> Left (ErrorMessage ann "expected a map mapping")
        _ -> Left (ErrorMessage ann "expected a map")
    -- NOTICE: what follows is the last Apply case. It is generic and must
    -- come last among all the Apply cases.
    OSL.Apply ann f x -> do
      fType <- inferType decls f
      case fType of
        OSL.F _ _ a _ -> do
          fM <- translateToMapping ctx fType f
          xM <- translateToMapping ctx a x
          Mapping <$> applyMappings ann ctx fM xM
        _ -> Left (ErrorMessage ann "expected a function")
    OSL.Let _ varName varType varDef body -> do
      varDefM <- translateToMapping ctx varType varDef
      let decls' = OSL.ValidContext
                     (Map.insert varName (OSL.Defined varType varDef) declsMap)
          ctx' = TranslationContext decls' (Map.insert varName varDefM mappings)
      translate ctx' termType body
    OSL.Equal ann x y -> do
      xType <- inferType decls x
      Formula <$> translateEquality ann ctx xType x y
    OSL.LessOrEqual _ x y -> do
      xType <- inferType decls x
      Formula <$>
        (S11.LessOrEqual
          <$> translateToTerm ctx xType x
          <*> translateToTerm ctx xType y)
    OSL.And _ p q ->
      Formula <$>
        (S11.And <$> translateToFormula ctx p
                 <*> translateToFormula ctx q)
    OSL.Or _ p q ->
      Formula <$>
        (S11.Or <$> translateToFormula ctx p
                <*> translateToFormula ctx q)
    OSL.Not _ p ->
      Formula . S11.Not <$> translateToFormula ctx p
    OSL.Implies _ p q ->
      Formula <$>
        (S11.Implies <$> translateToFormula ctx p
                     <*> translateToFormula ctx q)
    OSL.ForAll ann varName varType varBound p -> do
      varDim <- getMappingDimensions decls varType
      case varDim of
        FiniteDimensions n -> do
          let decls' = OSL.ValidContext
                $ Map.insert varName (OSL.FreeVariable varType) declsMap
          TranslationContext _ qCtx <-
            buildTranslationContext' decls' [varName]
          let ctx' = TranslationContext decls'
                     (qCtx `Map.union` (incrementDeBruijnIndices (Arity 0) n <$> mappings))
          bounds <- translateBound ctx varType varBound
          Formula . foldl (.) id (S11.ForAll <$> bounds)
            <$> translateToFormula ctx' p
        InfiniteDimensions ->
          Left (ErrorMessage ann "universal quantification over an infinite-dimensional type")
    OSL.ForSome _ varName varType varBound p -> do
     let decls' = OSL.ValidContext
          $ Map.insert varName (OSL.FreeVariable varType) declsMap
     varDim <- getMappingDimensions decls varType
     case varDim of
       FiniteDimensions n -> do
         TranslationContext _ qCtx <-
           buildTranslationContext' decls' [varName]
         let ctx' = TranslationContext decls'
                    (qCtx `Map.union` (incrementDeBruijnIndices (Arity 0) n <$> mappings))
         bounds <- translateBound ctx varType varBound
         Formula . foldl (.) id (S11.Exists . S11.ExistsFO <$> bounds)
           <$> translateToFormula ctx' p
       InfiniteDimensions -> do
         (qs, newMapping) <-
           getExistentialQuantifierStringAndMapping ctx varType
             =<< getExplicitOrInferredBound decls varType varBound
         let ctx' = TranslationContext decls'
                    (mergeMappings (Map.singleton varName newMapping) mappings)
         -- TODO: add additional conditions for map quantification
         Formula . (\f -> foldl' (flip S11.Exists) f qs)
           <$> translateToFormula ctx' p
    term -> Left (ErrorMessage (termAnnotation term) "could not translate term")


getExplicitOrInferredBound
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Maybe (OSL.Bound ann)
  -> Either (ErrorMessage ann) (OSL.Bound ann)
getExplicitOrInferredBound ctx t =
  maybe (inferBound ctx t) pure


getExistentialQuantifierStringAndMapping
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Bound ann
  -> Either (ErrorMessage ann)
     ([S11.ExistentialQuantifier], Mapping ann S11.Term)
getExistentialQuantifierStringAndMapping ctx@(TranslationContext decls mappings) varType varBound =
  case varType of
    OSL.Prop ann -> Left (ErrorMessage ann "cannot quantify over Prop")
    OSL.N _ -> scalarResult
    OSL.Z _ -> scalarResult
    OSL.Fin _ _ -> scalarResult
    OSL.F _ cardinality a b -> do
      aDim <- getMappingDimensions decls a
      case (aDim, varBound) of
        (FiniteDimensions n, OSL.FunctionBound _ (OSL.DomainBound aBound) (OSL.CodomainBound bBound)) -> do
          (bQs, bM) <-
            getExistentialQuantifierStringAndMapping
            ctx
            b
            bBound
          let fM = incrementArities n bM
          aBounds <- translateBound ctx a (Just aBound)
          let fQs = prependBounds cardinality aBounds <$> bQs
          pure (fQs, fM)
        (FiniteDimensions _, _) ->
          Left (ErrorMessage (boundAnnotation varBound)
                "expected a function bound")
        (InfiniteDimensions, _) ->
          Left (ErrorMessage (typeAnnotation a)
               "expected a finite-dimensional type")
    OSL.Product _ a b ->
      case varBound of
        OSL.ProductBound _ (OSL.LeftBound aBound) (OSL.RightBound bBound) -> do
          (aQs, aM) <- getExistentialQuantifierStringAndMapping ctx a aBound
          (bQs, bM) <- getExistentialQuantifierStringAndMapping ctx b bBound
          pure ( aQs <> bQs
               , mergeMapping
                 (\aM' bM' -> ProductMapping (LeftMapping aM') (RightMapping bM'))
                 bM aM )
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a product bound")
    OSL.Coproduct ann a b ->
      case varBound of
        OSL.CoproductBound _ (OSL.LeftBound aBound) (OSL.RightBound bBound) -> do
          let cQ = S11.ExistsFO (S11.Const 2)
              cT = S11.Var (S11.Name 0 0)
              cM = ChoiceMapping (ScalarMapping cT)
              cSym = getFreeOSLName ctx
              decls' = addDeclaration cSym (OSL.FreeVariable (OSL.Fin ann 2)) decls
              ctx' = TranslationContext decls' mappings
          -- TODO: can this result in overlap between cM and bM/aM?
          ctx'' <- runIdentity . runExceptT
            $ execStateT (addFreeVariableMapping cSym) ctx'
          (aQs, aM) <- getExistentialQuantifierStringAndMapping ctx'' a aBound
          (bQs, bM) <- getExistentialQuantifierStringAndMapping ctx'' b bBound
          pure ( [cQ] <> aQs <> bQs
               , mergeMapping
                 (\bM' aM' -> CoproductMapping cM (LeftMapping aM') (RightMapping bM'))
                 bM aM )
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a coproduct bound")
    OSL.NamedType ann name ->
      case varBound of
        OSL.ToBound _ name' aBound ->
          if name == name'
          then case getDeclaration decls name of
                 Just (OSL.Data a) ->
                   getExistentialQuantifierStringAndMapping ctx a aBound
                 _ -> Left (ErrorMessage ann "expected the name of a type")
          else Left (ErrorMessage ann "named type mismatch in bound")
        OSL.ScalarBound _ _ -> scalarResult
        _ -> Left (ErrorMessage ann ("expected a " <> pack (show name) <> " bound"))
    OSL.Maybe _ a ->
      case varBound of
        OSL.MaybeBound _ (OSL.ValuesBound aBound) -> do
          let cQ = S11.ExistsFO (S11.Const 2)
              cM = ScalarMapping (S11.Var (S11.Name 0 0))
          (vQs, vM) <- getExistentialQuantifierStringAndMapping ctx a aBound
          pure (cQ : vQs, MaybeMapping (ChoiceMapping cM) (ValuesMapping vM))
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a maybe bound")
    OSL.List ann (OSL.Cardinality n) a ->
      case varBound of
        OSL.ListBound _ (OSL.ValuesBound aBound) -> do
          let lQ = S11.ExistsFO (S11.Const n)
              lT = S11.Var (S11.Name 0 0)
              lSym = getFreeOSLName ctx
              decls' = addDeclaration lSym (OSL.FreeVariable (OSL.N ann)) decls
              ctx' = TranslationContext decls' mappings
          ctx'' <- runIdentity . runExceptT
            $ execStateT (addFreeVariableMapping lSym) ctx'
          (vQs, vM) <-
            getExistentialQuantifierStringAndMapping
            ctx''
            (OSL.F ann (Just (OSL.Cardinality n)) (OSL.N ann) a)
            (OSL.FunctionBound ann
               (OSL.DomainBound (OSL.ScalarBound ann (OSL.NamedTerm ann lSym)))
               (OSL.CodomainBound aBound))
          pure ( lQ : vQs
               , ListMapping
                 (LengthMapping (ScalarMapping lT))
                 (ValuesMapping vM) )
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a list bound")
    OSL.Map ann (OSL.Cardinality n) a b ->
      case varBound of
        OSL.MapBound _ (OSL.KeysBound aBound) (OSL.ValuesBound bBound) -> do
          (kQs, kM) <- getExistentialQuantifierStringAndMapping
            ctx
            (OSL.List ann (OSL.Cardinality n) a)
            (OSL.ListBound ann (OSL.ValuesBound aBound))
          (vQs, vM) <- getExistentialQuantifierStringAndMapping
            ctx
            (OSL.F ann Nothing a b)
            (OSL.FunctionBound ann
              (OSL.DomainBound aBound)
              (OSL.CodomainBound bBound))
          pure ( kQs <> vQs
               , mergeMapping
                 (curry (\case
                    ( ListMapping (LengthMapping lM) (ValuesMapping kM''),
                      MaybeMapping (ChoiceMapping cM) (ValuesMapping vM'') ) ->
                      MapMapping (LengthMapping lM) (KeysMapping kM'')
                                 (KeyIndicatorMapping cM) (ValuesMapping vM'')
                    _ -> die "logical impossibility in map quantifier translation"))
                 kM vM )
        _ -> Left (ErrorMessage ann "expected a map bound")
  where
    scalarResult =
      case varBound of
        OSL.ScalarBound _ _ -> do
          bTs <- translateBound ctx varType (Just varBound)
          case bTs of
            [bT] -> 
              pure ( [S11.ExistsFO bT]
                   , ScalarMapping (S11.Var (S11.Name 0 0)) )
            _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a scalar bound")
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a scalar bound")


getMappingDimensions
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Either (ErrorMessage ann) MappingDimensions
getMappingDimensions ctx t =
  case t of
    OSL.Prop ann -> Left (ErrorMessage ann "expected a quantifiable type; got Prop")
    OSL.F _ _ _ _ -> pure InfiniteDimensions
    OSL.N _ -> pure (FiniteDimensions 1)
    OSL.Z _ -> pure (FiniteDimensions 1)
    OSL.Fin _ _ -> pure (FiniteDimensions 1)
    OSL.Product _ a b ->
      (<>) <$> getMappingDimensions ctx a
           <*> getMappingDimensions ctx b
    OSL.Coproduct _ a b ->
      (FiniteDimensions 1 <>)
      <$> ((<>) <$> getMappingDimensions ctx a
                <*> getMappingDimensions ctx b)
    OSL.Maybe _ a ->
      (FiniteDimensions 1 <>) <$> getMappingDimensions ctx a
    OSL.NamedType ann a ->
      case getDeclaration ctx a of
        Just (OSL.Data b) -> getMappingDimensions ctx b
        _ -> Left (ErrorMessage ann "expected the name of a type")
    OSL.List _ _ _ -> pure InfiniteDimensions
    OSL.Map _ _ _ _ -> pure InfiniteDimensions


getArbitraryMapping
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Either (ErrorMessage ann) (Mapping ann S11.Term)
getArbitraryMapping ctx =
  \case
    OSL.Prop ann -> Left (ErrorMessage ann "expected a finite-dimensional type; got a Prop")
    OSL.F ann _ _ _ -> Left (ErrorMessage ann "expected a finite-dimensional type; got a function")
    OSL.N _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Z _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Fin _ _ -> return $ ScalarMapping (S11.Const 0)
    OSL.Product _ a b ->
      ProductMapping
      <$> (LeftMapping <$> rec a)
      <*> (RightMapping <$> rec b)
    OSL.Coproduct _ a b ->
      CoproductMapping (ChoiceMapping (ScalarMapping (S11.Const 0)))
      <$> (LeftMapping <$> rec a)
      <*> (RightMapping <$> rec b)
    OSL.Maybe _ a ->
      MaybeMapping (ChoiceMapping (ScalarMapping (S11.Const 0)))
      . ValuesMapping <$> rec a
    OSL.NamedType ann a ->
      case getDeclaration ctx a of
        Just (OSL.Data b) -> rec b
        Just _ -> Left (ErrorMessage ann "expected the name of a type")
        Nothing -> Left (ErrorMessage ann "undefined name")
    OSL.List ann _ _ -> Left (ErrorMessage ann "expected a finite-dimensional type; got a List")
    OSL.Map ann _ _ _ -> Left (ErrorMessage ann "expected a finite-dimensional type; got a Map")
  where
    rec = getArbitraryMapping ctx      


translateToMapping
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) (Mapping ann S11.Term)
translateToMapping c tType t =
  case translate c tType t of
    Right (Mapping m) -> return m
    Right (Term t') -> pure (ScalarMapping t')
    Right (Formula p) -> pure (PropMapping p)
    Left err -> Left err
    

translateToTerm
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) S11.Term
translateToTerm c tType t =
  case translate c tType t of
    Right (Term t') -> return t'
    Right (Mapping (ScalarMapping t')) -> return t'
    Right _ -> Left (ErrorMessage (termAnnotation t)
                 "expected a term denoting a scalar or a scalar function")
    Left err -> Left err


translateToFormula
  :: Show ann
  => TranslationContext ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) S11.Formula
translateToFormula c t =
  case translate c (OSL.Prop (termAnnotation t)) t of
    Right (Formula f) -> pure f
    Right (Mapping (PropMapping f)) -> pure f
    Right (Mapping (LambdaMapping (TranslationContext decls mappings) _ _ _)) ->
      case t of
        OSL.Lambda _ varName varType body -> do
          let decls' = addDeclaration varName (OSL.FreeVariable varType) decls
              ctx' = TranslationContext decls' mappings
          ctx'' <- runIdentity . runExceptT
            $ execStateT (addFreeVariableMapping varName) ctx'
          translateToFormula ctx'' body
        _ -> Left (ErrorMessage (termAnnotation t)
              "lambda mapping for a non-lambda (this is a compiler bug")
    Right _ -> Left (ErrorMessage (termAnnotation t)
                 "expected a term denoting a Prop")
    Left err -> Left err


applyMappings
  :: Show ann
  => ann
  -> TranslationContext ann
  -> Mapping ann S11.Term
  -> Mapping ann S11.Term
  -> Either (ErrorMessage ann) (Mapping ann S11.Term)
applyMappings ann ctx f x =
  case (f, x) of
    (LambdaMapping (TranslationContext decls mappings) v vT t, _) -> do
      let decls' = addDeclaration v (OSL.FreeVariable vT) decls
          ctx' = TranslationContext decls' mappings
      ctx'' <- runIdentity . runExceptT
               $ execStateT (addTermMapping v x) ctx'
      tT <- inferType decls' t
      translateToMapping ctx'' tT t
    (ScalarMapping f', ScalarMapping x') ->
      ScalarMapping <$> applyTerms ann f' x'
    (f', ProductMapping (LeftMapping x') (RightMapping y')) -> do
      f'' <- applyMappings ann ctx f' x'
      applyMappings ann ctx f'' y'
    (ProductMapping (LeftMapping g) (RightMapping h), x') ->
      ProductMapping
      <$> (LeftMapping <$> applyMappings ann ctx g x')
      <*> (RightMapping <$> applyMappings ann ctx h x')
    (MaybeMapping (ChoiceMapping g) (ValuesMapping h), x') ->
      MaybeMapping
      <$> (ChoiceMapping <$> applyMappings ann ctx g x')
      <*> (ValuesMapping <$> applyMappings ann ctx h x')
    (FunctionCoproductMapping (LeftMapping g) (RightMapping h),
     CoproductMapping (ChoiceMapping a) (LeftMapping b) (RightMapping d)) ->
      CoproductMapping (ChoiceMapping a)
      <$> (LeftMapping <$> applyMappings ann ctx g b)
      <*> (RightMapping <$> applyMappings ann ctx h d)
    _ -> Left (ErrorMessage ann ("unable to apply mappings:\n" <> pack (show f) <> "\n<---\n" <> pack (show x)))


applyTerms
  :: ann
  -> S11.Term
  -> S11.Term
  -> Either (ErrorMessage ann) S11.Term
applyTerms ann f x =
  case f of
    S11.Var f' -> pure $ S11.App f' [x]
    S11.App f' ys -> pure $ S11.App f' (ys <> [x])
    _ -> Left $ ErrorMessage ann
      ("expected a function term; got " <> pack (show f))


translateBound
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> Maybe (OSL.Bound ann)
  -> Either (ErrorMessage ann) [S11.Term]
translateBound ctx@(TranslationContext decls _) t =
  \case
    Just (OSL.ScalarBound _ term) -> (:[]) <$> translateToTerm ctx t term
    Just (OSL.ProductBound ann (OSL.LeftBound aBound) (OSL.RightBound bBound)) ->
      case t of
        OSL.Product _ a b ->
          (<>) <$> translateBound ctx a (Just aBound)
               <*> translateBound ctx b (Just bBound)
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.ToBound ann name bound) ->
      case getDeclaration decls name of
        Just (OSL.Data a) -> translateBound ctx a (Just bound)
        Just _ -> Left . ErrorMessage ann $ "expected the name of a type"
        Nothing -> Left . ErrorMessage ann $ "undefined name"
    Just (OSL.CoproductBound ann (OSL.LeftBound aBound) (OSL.RightBound bBound)) ->
      case t of 
        OSL.Coproduct _ a b ->
          (<>) <$> translateBound ctx a (Just aBound)
               <*> translateBound ctx b (Just bBound)
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.FunctionBound ann
            (OSL.DomainBound aBound)
            (OSL.CodomainBound bBound)) ->
      case t of
        OSL.F _ _ a b ->
          (<>) <$> translateBound ctx a (Just aBound)
               <*> translateBound ctx b (Just bBound)
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.ListBound ann (OSL.ValuesBound vBound)) ->
      case t of
        OSL.List ann' n'@(OSL.Cardinality n) a ->
          let lBound = OSL.ScalarBound ann' (OSL.ConstN ann n) in
          (<>) <$> translateBound ctx (OSL.N ann') (Just lBound)
               <*> translateBound ctx (OSL.F ann' (Just n') (OSL.N ann') a)
                   (Just
                     (OSL.FunctionBound ann
                       (OSL.DomainBound lBound)
                       (OSL.CodomainBound vBound)))
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.MaybeBound ann (OSL.ValuesBound vBound)) ->
      case t of
        OSL.Maybe _ a ->
          ((S11.Const 2):) <$> translateBound ctx a (Just vBound)
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Just (OSL.MapBound ann
            (OSL.KeysBound kBound)
            (OSL.ValuesBound vBound)) ->
      case t of
        OSL.Map ann' n'@(OSL.Cardinality n) k v ->
          mconcatM
          [ translateBound ctx (OSL.N ann') (Just (OSL.ScalarBound ann' (OSL.ConstN ann' n)))
          , translateBound ctx (OSL.F ann' (Just n') (OSL.N ann') k)
              (Just (OSL.FunctionBound ann'
                 (OSL.DomainBound (OSL.ScalarBound ann' (OSL.ConstN ann' n)))
                 (OSL.CodomainBound kBound)))
          , translateBound ctx (OSL.F ann' (Just n') k (OSL.N ann'))
              (Just (OSL.FunctionBound ann' (OSL.DomainBound kBound)
                (OSL.CodomainBound (OSL.ScalarBound ann' (OSL.ConstN ann' 2)))))
          , translateBound ctx (OSL.F ann' (Just n') k v)
              (Just (OSL.FunctionBound ann'
                (OSL.DomainBound kBound)
                (OSL.CodomainBound vBound)))
          ]
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    Nothing -> translateBound ctx t . Just =<< inferBound decls t


inferBound
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Either (ErrorMessage ann) (OSL.Bound ann)
inferBound ctx =
  \case
    OSL.Prop ann -> Left (ErrorMessage ann "expected a quantifiable type but got Prop")
    OSL.F ann _ a b ->
      OSL.FunctionBound ann
      <$> (OSL.DomainBound <$> inferBound ctx a)
      <*> (OSL.CodomainBound <$> inferBound ctx b)
    OSL.N ann -> Left (ErrorMessage ann "cannot infer bound for N")
    OSL.Z ann -> Left (ErrorMessage ann "cannot infer bound for Z")
    OSL.Fin ann n -> pure (OSL.ScalarBound ann (OSL.ConstN ann n))
    OSL.Product ann a b ->
      OSL.ProductBound ann
      <$> (OSL.LeftBound <$> inferBound ctx a)
      <*> (OSL.RightBound <$> inferBound ctx b)
    OSL.Coproduct ann a b ->
      OSL.CoproductBound ann
      <$> (OSL.LeftBound <$> inferBound ctx a)
      <*> (OSL.RightBound <$> inferBound ctx b)
    OSL.NamedType ann name ->
      case getDeclaration ctx name of
        Just (OSL.Data a) ->
          OSL.ToBound ann name <$> inferBound ctx a
        _ -> Left (ErrorMessage ann "expected the name of a type")
    OSL.Maybe ann a ->
      OSL.MaybeBound ann . OSL.ValuesBound 
        <$> inferBound ctx a
    OSL.List ann _ a ->
      OSL.ListBound ann . OSL.ValuesBound
        <$> inferBound ctx a
    OSL.Map ann _ a b ->
      OSL.MapBound ann
      <$> (OSL.KeysBound <$> inferBound ctx a)
      <*> (OSL.ValuesBound <$> inferBound ctx b)


translateEquality
  :: Show ann
  => ann
  -> TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) S11.Formula
translateEquality ann ctx t x y = do
  xM <- translateToMapping ctx t x
  yM <- translateToMapping ctx t y
  applyEqualityToMappings ann t xM yM


applyEqualityToMappings
  :: ann
  -> OSL.Type ann
  -> Mapping ann S11.Term
  -> Mapping ann S11.Term
  -> Either (ErrorMessage ann) S11.Formula
applyEqualityToMappings ann t x y =
  case (x,y,t) of
    (ScalarMapping xT, ScalarMapping yT, _) ->
      pure (S11.Equal xT yT)
    (ProductMapping (LeftMapping xlM) (RightMapping xrM),
     ProductMapping (LeftMapping ylM) (RightMapping yrM),
     OSL.Product _ a b) ->
      S11.And
      <$> applyEqualityToMappings ann a xlM ylM
      <*> applyEqualityToMappings ann b xrM yrM
    (CoproductMapping
      (ChoiceMapping (ScalarMapping xcM))
      (LeftMapping xlM)
      (RightMapping xrM),
     CoproductMapping
      (ChoiceMapping (ScalarMapping ycM))
      (LeftMapping ylM)
      (RightMapping yrM),
     OSL.Coproduct _ a b) ->
      S11.And (S11.Equal xcM ycM)
      <$> (S11.Or
          <$> (S11.And (S11.Equal xcM (S11.Const 0))
               <$> applyEqualityToMappings ann a xlM ylM)
          <*> (S11.And (S11.Equal xcM (S11.Const 1))
               <$> applyEqualityToMappings ann b xrM yrM))
    (MaybeMapping (ChoiceMapping (ScalarMapping xcM))
        (ValuesMapping xvM),
      MaybeMapping (ChoiceMapping (ScalarMapping ycM))
        (ValuesMapping yvM),
      OSL.Maybe _ a) ->
       S11.And (S11.Equal xcM ycM)
       . S11.Or (S11.Equal xcM (S11.Const 0))
       <$> applyEqualityToMappings ann a xvM yvM
    _ -> Left (ErrorMessage ann "cannot compare these things for equality")


mconcatM :: Monad m => Monoid a => [m a] -> m a
mconcatM [] = return mempty
mconcatM (xM:xMs) = do
  x <- xM
  (x <>) <$> mconcatM xMs
