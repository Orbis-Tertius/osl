{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}


module OSL.Translate
  ( translate
  ) where


import Control.Applicative (liftA2)
import Data.List (foldl')
import qualified Data.Map as Map
import Data.Text (pack)

import OSL.BuildTranslationContext (buildTranslationContext')
import OSL.Sigma11 (incrementDeBruijnIndices, incrementArities)
import OSL.Term (termAnnotation, boundAnnotation)
import OSL.TranslationContext (mappingDimensions, mergeMappings, mergeMapping)
import OSL.Types.Arity (Arity (..))
import OSL.Types.ErrorMessage (ErrorMessage (..))
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Sigma11 as S11
import OSL.Types.Translation (Translation (Formula, Term, Mapping))
import OSL.Types.TranslationContext (TranslationContext (..), Mapping (..), LeftMapping (..), RightMapping (..), ChoiceMapping (..), ValuesMapping (..), MappingDimensions (..), LengthMapping (..), KeyIndicatorMapping (..), KeysMapping (..))
import OSL.ValidContext (getDeclaration)
import OSL.ValidateContext (inferType)


-- Provides a translation for the given term in
-- the given context.
translate
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Term ann
  -> Either (ErrorMessage ann) Translation
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
    OSL.Apply _ (OSL.Lambda _ varName varType body) x -> do
      xM <- translateToMapping ctx varType x
      let decls' = OSL.ValidContext
                     (Map.insert varName (OSL.Defined varType x) declsMap)
          ctx' = TranslationContext decls' (Map.insert varName xM mappings)
      Mapping <$> translateToMapping ctx' termType body
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
              fvM <- applyMappings ann fM vM
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
      Mapping <$> applyMappings ann xsM (const iT <$> xsM)
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
              kExistsM <- applyMappings ann indM kM
              vM' <- applyMappings ann vM kM
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
          Mapping <$> applyMappings ann fM xM
        _ -> Left (ErrorMessage ann "expected a function")
    OSL.Let _ varName varType varDef body -> do
      varDefM <- translateToMapping ctx varType varDef
      let decls' = OSL.ValidContext
                     (Map.insert varName (OSL.Defined varType varDef) declsMap)
          ctx' = TranslationContext decls' (Map.insert varName varDefM mappings)
      Mapping <$> translateToMapping ctx' termType body
    OSL.Equal _ x y -> do
      xType <- inferType decls x
      Formula <$>
        (S11.Equal
          <$> translateToTerm ctx xType x
          <*> translateToTerm ctx xType y)
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
           getExistentialQuantifierStringAndMapping ctx varType varBound
         let ctx' = TranslationContext decls'
                    (mergeMappings (Map.singleton varName newMapping) mappings)
         Formula . (\f -> foldl' (flip S11.Exists) f qs)
           <$> translateToFormula ctx' p


getExistentialQuantifierStringAndMapping
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Bound ann
  -> Either (ErrorMessage ann)
     ([S11.ExistentialQuantifier], Mapping S11.Term)
getExistentialQuantifierStringAndMapping ctx@(TranslationContext decls _) varType varBound =
  case varType of
    OSL.Prop ann -> Left (ErrorMessage ann "cannot quantify over Prop")
    OSL.N _ -> scalarResult
    OSL.Z _ -> scalarResult
    OSL.Fin _ _ -> scalarResult
    OSL.Product _ a b ->
      case varBound of
        OSL.ProductBound _ (OSL.LeftBound aBound) (OSL.RightBound bBound) -> do
          (aQs, aM) <- getExistentialQuantifierStringAndMapping ctx a aBound
          (bQs, bM) <- getExistentialQuantifierStringAndMapping ctx b bBound
          pure (aQs <> bQs, mergeMapping bM aM)
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a product bound")
    OSL.Coproduct _ a b ->
      case varBound of
        OSL.CoproductBound _ (OSL.LeftBound aBound) (OSL.RightBound bBound) -> do
          (aQs, aM) <- getExistentialQuantifierStringAndMapping ctx a aBound
          (bQs, bM) <- getExistentialQuantifierStringAndMapping ctx b bBound
          pure (aQs <> bQs, mergeMapping bM aM)
    OSL.NamedType ann name ->
      case varBound of
        OSL.ToBound _ name' aBound ->
          if name == name'
          then case getDeclaration decls name of
                 Just (OSL.Data a) ->
                   getExistentialQuantifierStringAndMapping ctx a aBound
                 _ -> Left (ErrorMessage ann "expected the name of a type")
          else Left (ErrorMessage ann "named type mismatch in bound")
        OSL.ScalarBound _ bT -> scalarResult
        _ -> Left (ErrorMessage ann ("expected a " <> pack (show name) <> " bound"))
    OSL.Maybe _ a ->
      case varBound of
        OSL.MaybeBound _ (OSL.ValuesBound aBound) -> do
          let cQ = S11.ExistsFO (S11.Const 2)
              cM = ScalarMapping (S11.Var (S11.Name 0 0))
          (vQs, vM) <- getExistentialQuantifierStringAndMapping ctx a aBound
          pure (cQ : vQs, MaybeMapping (ChoiceMapping cM) (ValuesMapping vM))
    OSL.List _ (OSL.Cardinality n) a ->
      case varBound of
        OSL.ListBound _ (OSL.ValuesBound aBound) -> do
          let lQ = S11.ExistsFO (S11.Const n)
              lM = ScalarMapping (S11.Var (S11.Name 0 0))
          (vQs, vM) <- getExistentialQuantifierStringAndMapping ctx a aBound
          pure
            ( lQ : vQs
            , ListMapping
              (LengthMapping lM)
              (ValuesMapping (incrementArities 1 vM)))
  where
    scalarResult =
      case varBound of
        OSL.ScalarBound _ b -> do
          bTs <- translateBound ctx varType varBound
          case bTs of
            [bT] -> 
              pure ( [S11.ExistsFO bT]
                   , ScalarMapping bT )
            _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a scalar bound")
        _ -> Left (ErrorMessage (boundAnnotation varBound) "expected a scalar bound")


getMappingDimensions
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Either (ErrorMessage ann) MappingDimensions
getMappingDimensions ctx t =
  mappingDimensions <$> getArbitraryMapping ctx t


getArbitraryMapping
  :: OSL.ValidContext ann
  -> OSL.Type ann
  -> Either (ErrorMessage ann) (Mapping S11.Term)
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
  -> Either (ErrorMessage ann) (Mapping S11.Term)
translateToMapping c tType t =
  case translate c tType t of
    Right (Mapping m) -> return m
    Right (Term t') -> return (ScalarMapping t')
    Right (Formula _) ->
      Left (ErrorMessage (termAnnotation t)
             "expected a value but got a proposition")
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
    Right (Formula f) -> return f
    Right _ -> Left (ErrorMessage (termAnnotation t)
                 "expected a term denoting a Prop")
    Left err -> Left err


applyMappings
  :: ann
  -> Mapping S11.Term
  -> Mapping S11.Term
  -> Either (ErrorMessage ann) (Mapping S11.Term)
applyMappings ann f x =
  case (f, x) of
    (ScalarMapping f', ScalarMapping x') ->
      ScalarMapping <$> applyTerms ann f' x'
    (ProductMapping (LeftMapping g) (RightMapping h), x') ->
      ProductMapping
      <$> (LeftMapping <$> applyMappings ann g x')
      <*> (RightMapping <$> applyMappings ann h x')
    (FunctionCoproductMapping (LeftMapping g) (RightMapping h),
     CoproductMapping (ChoiceMapping a) (LeftMapping b) (RightMapping d)) ->
      CoproductMapping (ChoiceMapping a)
      <$> (LeftMapping <$> applyMappings ann g b)
      <*> (RightMapping <$> applyMappings ann h d)
    _ -> Left (ErrorMessage ann "unable to apply mappings")


applyTerms
  :: ann
  -> S11.Term
  -> S11.Term
  -> Either (ErrorMessage ann) S11.Term
applyTerms ann f x =
  case f of
    S11.Var f' -> pure $ S11.App f' [x]
    S11.App f' ys -> pure $ S11.App f' (ys <> [x])
    _ -> Left $ ErrorMessage ann "expected a function term"


translateBound
  :: Show ann
  => TranslationContext ann
  -> OSL.Type ann
  -> OSL.Bound ann
  -> Either (ErrorMessage ann) [S11.Term]
translateBound ctx@(TranslationContext decls _) t =
  \case
    OSL.ScalarBound _ term -> (:[]) <$> translateToTerm ctx t term
    OSL.ProductBound ann (OSL.LeftBound aBound) (OSL.RightBound bBound) ->
      case t of
        OSL.Product _ a b ->
          (<>) <$> translateBound ctx a aBound
               <*> translateBound ctx b bBound
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    OSL.ToBound ann name bound ->
      case getDeclaration decls name of
        Just (OSL.Data a) -> translateBound ctx a bound
        Just _ -> Left . ErrorMessage ann $ "expected the name of a type"
        Nothing -> Left . ErrorMessage ann $ "undefined name"
    OSL.CoproductBound ann (OSL.LeftBound aBound) (OSL.RightBound bBound) ->
      case t of 
        OSL.Coproduct _ a b ->
          (<>) <$> translateBound ctx a aBound
               <*> translateBound ctx b bBound
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    OSL.FunctionBound ann (OSL.DomainBound aBound)
                          (OSL.CodomainBound bBound) ->
      case t of
        OSL.F _ _ a b ->
          (<>) <$> translateBound ctx a aBound
               <*> translateBound ctx b bBound
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    OSL.ListBound ann (OSL.ValuesBound vBound) ->
      case t of
        OSL.List ann' n'@(OSL.Cardinality n) a ->
          let lBound = OSL.ScalarBound ann' (OSL.ConstN ann n) in
          (<>) <$> translateBound ctx (OSL.N ann') lBound
               <*> translateBound ctx (OSL.F ann' (Just n') (OSL.N ann') a)
                   (OSL.FunctionBound ann
                     (OSL.DomainBound lBound)
                     (OSL.CodomainBound vBound))
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    OSL.MaybeBound ann (OSL.ValuesBound vBound) ->
      case t of
        OSL.Maybe _ a ->
          ((S11.Const 2):) <$> translateBound ctx a vBound
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)
    OSL.MapBound ann
        (OSL.KeysBound kBound)
        (OSL.ValuesBound vBound) ->
      case t of
        OSL.Map ann' n'@(OSL.Cardinality n) k v ->
          mconcatM
          [ translateBound ctx (OSL.N ann') (OSL.ScalarBound ann' (OSL.ConstN ann' n))
          , translateBound ctx (OSL.F ann' (Just n') (OSL.N ann') k)
              (OSL.FunctionBound ann'
                 (OSL.DomainBound (OSL.ScalarBound ann' (OSL.ConstN ann' n)))
                 (OSL.CodomainBound kBound))
          , translateBound ctx (OSL.F ann' (Just n') k (OSL.N ann'))
              (OSL.FunctionBound ann' (OSL.DomainBound kBound)
                (OSL.CodomainBound (OSL.ScalarBound ann' (OSL.ConstN ann' 2))))
          , translateBound ctx (OSL.F ann' (Just n') k v)
              (OSL.FunctionBound ann'
                (OSL.DomainBound kBound)
                (OSL.CodomainBound vBound))
          ]
        _ -> Left . ErrorMessage ann $ "expected a " <> pack (show t)


mconcatM :: Monad m => Monoid a => [m a] -> m a
mconcatM [] = return mempty
mconcatM (xM:xMs) = do
  x <- xM
  (x <>) <$> mconcatM xMs


todo :: a
todo = todo
