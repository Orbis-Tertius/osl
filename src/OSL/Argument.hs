{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module OSL.Argument (toSigma11Argument) where

import Cast (intToInteger)
import Control.Lens ((^.))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified OSL.Sigma11 as S11
import OSL.Types.ErrorMessage (ErrorMessage (ErrorMessage))
import OSL.Evaluation (decodeScalar)
import qualified OSL.Type as OSL
import qualified OSL.Types.ArgumentForm as OSL
import qualified OSL.Types.Argument as OSL
import qualified OSL.Types.OSL as OSL
import qualified OSL.Types.Value as OSL
import qualified OSL.Types.Sigma11.Argument as S11
import qualified OSL.Types.Sigma11.Value as S11
import qualified OSL.Types.Sigma11.ValueTree as S11
import qualified OSL.Value as OSL
import Safe (atMay)
import Stark.Types.Scalar (Scalar, zero, one, integerToScalar)

toSigma11Argument ::
  OSL.ValidContext t ann ->
  OSL.ArgumentForm ->
  OSL.Argument ->
  OSL.Term () ->
  Either (ErrorMessage ()) S11.Argument
toSigma11Argument c af a x =
  S11.Argument
    <$> toSigma11Statement c (af ^. #statementType) (a ^. #statement)
    <*> toSigma11Witness c (af ^. #witnessType) (a ^. #witness) x
toSigma11Statement ::
  OSL.ValidContext t ann ->
  OSL.StatementType ->
  OSL.Statement ->
  Either (ErrorMessage ()) S11.Statement
toSigma11Statement c (OSL.StatementType t) (OSL.Statement s) =
  S11.Statement <$> toSigma11Values c t s

scalarValue :: Scalar -> S11.Value
scalarValue = S11.Value . Map.singleton []

toSigma11Witness ::
  OSL.ValidContext t ann ->
  OSL.WitnessType ->
  OSL.Witness ->
  OSL.Term () ->
  Either (ErrorMessage ()) S11.Witness
toSigma11Witness c (OSL.WitnessType t) (OSL.Witness w) x =
  S11.Witness <$> toSigma11ValueTree c t w x

toSigma11ValueTree ::
  OSL.ValidContext t ann ->
  OSL.Type () ->
  OSL.Value ->
  OSL.Term () ->
  Either (ErrorMessage ()) S11.ValueTree
toSigma11ValueTree c t val term =
  case (t,val,term) of
    (OSL.Product _ a b, OSL.Pair' x y, OSL.And _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.And {}) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y, OSL.Or _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.Or {}) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y, OSL.Implies _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.Implies {}) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y, OSL.Iff _ p q) ->
      pairTree <$> rec a x p <*> rec b y q
    (_, _, OSL.Iff {}) -> typeMismatch
    (_, _, OSL.Equal {}) -> pure emptyTree
    (_, _, OSL.LessOrEqual {}) -> pure emptyTree
    (_, _, OSL.Top _) -> pure emptyTree
    (_, _, OSL.Bottom _) -> pure emptyTree
    (OSL.Prop _, _, _) -> typeMismatch
    (OSL.F _ _ (OSL.N _) b, OSL.Fun f, OSL.ForAll _ _ (OSL.N _) _ p) ->
      scalarForAll b f p
    (OSL.F _ _ (OSL.Z _) b, OSL.Fun f, OSL.ForAll _ _ (OSL.Z _) _ p) ->
      scalarForAll b f p
    (OSL.F _ _ (OSL.Fp _) b, OSL.Fun f, OSL.ForAll _ _ (OSL.Fp _) _ p) ->
       scalarForAll b f p
    (OSL.F _ _ (OSL.Fin {}) b, OSL.Fun f, OSL.ForAll _ _ (OSL.Fin {}) _ p) ->
      scalarForAll b f p
    (OSL.F _ _ (OSL.Product _ a b) d, OSL.Fun f, OSL.ForAll _ x (OSL.Product {}) _ p) -> do
      f' <- curryFun f
      rec (OSL.F () Nothing a (OSL.F () Nothing b d))
        (OSL.Fun f')
        -- Note that this step, and similar steps below, corrupt the input term by changing the usage of x,
        -- and also by removing any bounds on x, but none of that matters for this algorithm,
        -- where the atomic formulas and also the quantifier bounds are irrelevant.
        (OSL.ForAll () x a Nothing (OSL.ForAll () x b Nothing p))
    (OSL.F _ _ (OSL.Coproduct _ a b) d, OSL.Fun f, OSL.ForAll _ x (OSL.Coproduct {}) _ p) -> do
      defaultA <- OSL.defaultValue c a
      defaultB <- OSL.defaultValue c b
      f' <- curryCoproductFun (defaultA, defaultB) f
      rec (OSL.F () Nothing (OSL.N ()) (OSL.F () Nothing a (OSL.F () Nothing b d)))
        (OSL.Fun f')
        (OSL.ForAll () x (OSL.N ()) Nothing
          (OSL.ForAll () x a Nothing
            (OSL.ForAll () x b Nothing p)))
    (OSL.F _ _ (OSL.Maybe _ a) b, OSL.Fun f, OSL.ForAll _ x (OSL.Maybe {}) _ p) -> do
      defaultA <- OSL.defaultValue c a
      f' <- curryMaybeFun defaultA f
      rec (OSL.F () Nothing (OSL.N ()) (OSL.F () Nothing a b))
        (OSL.Fun f')
        (OSL.ForAll () x (OSL.N ()) Nothing (OSL.ForAll () x a Nothing p))
    (OSL.Product () (OSL.N _) b, OSL.Pair' x y, OSL.ForSome _ _ (OSL.N _) _ p) -> do
      S11.ValueTree <$> (Just . S11.Value . Map.singleton [] <$> decodeScalar () x)
                    <*> ((:[]) <$> rec b y p)
  where
    rec = toSigma11ValueTree c

    pairTree x y = S11.ValueTree Nothing [x, y]

    emptyTree = S11.ValueTree Nothing []

    scalarForAll b f p =
      -- we are relying on Map.elems outputting the elements in ascending
      -- order of their keys
      S11.ValueTree Nothing <$> sequence
        [ rec b y p | y <- Map.elems f ]

curryFun :: Map OSL.Value OSL.Value -> Either (ErrorMessage ()) (Map OSL.Value OSL.Value)
curryFun f =
  fmap OSL.Fun . Map.unionsWith (<>) <$> sequence
    [ case x of
        OSL.Pair' x0 x1 -> pure (Map.singleton x0 (Map.singleton x1 y))
        _ -> typeMismatch
    | (x,y) <- Map.toList f
    ]

curryCoproductFun :: (OSL.Value, OSL.Value) -> Map OSL.Value OSL.Value -> Either (ErrorMessage ()) (Map OSL.Value OSL.Value)
curryCoproductFun (defaultLeft, defaultRight) f =
  fmap OSL.Fun . fmap (fmap OSL.Fun) . Map.unionsWith (Map.unionWith (<>)) <$> sequence
    [ case x of
        OSL.Iota1' x' -> pure (Map.singleton (OSL.Nat zero) (Map.singleton x' (Map.singleton defaultRight y)))
        OSL.Iota2' x' -> pure (Map.singleton (OSL.Nat one) (Map.singleton defaultLeft (Map.singleton x' y)))
        _ -> typeMismatch
    | (x,y) <- Map.toList f
    ]

curryMaybeFun :: OSL.Value -> Map OSL.Value OSL.Value -> Either (ErrorMessage ()) (Map OSL.Value OSL.Value)
curryMaybeFun defaultValue f =
  fmap OSL.Fun . Map.unionsWith (<>) <$> sequence
    [ case x of
        OSL.Maybe'' Nothing -> pure (Map.singleton (OSL.Nat zero) (Map.singleton defaultValue y))
        OSL.Maybe'' (Just x') -> pure (Map.singleton (OSL.Nat one) (Map.singleton x' y))
        _ -> typeMismatch
    | (x,y) <- Map.toList f
    ]

toSigma11Values ::
  OSL.ValidContext t ann ->
  OSL.Type () ->
  OSL.Value ->
  Either (ErrorMessage ()) [S11.Value]
toSigma11Values c t v =
  case (t, v) of
    (OSL.N _, OSL.Nat x) -> pure [scalarValue x]
    (OSL.N _, _) -> typeMismatch
    (OSL.Z _, OSL.Int x) -> pure [scalarValue x]
    (OSL.Z _, _) -> typeMismatch
    (OSL.Fp _, OSL.Fp' x) -> pure [scalarValue x]
    (OSL.Fp _, _) -> typeMismatch
    (OSL.Fin {}, OSL.Fin' x) -> pure [scalarValue x]
    (OSL.Fin {}, _) -> typeMismatch
    (OSL.Product _ a b, OSL.Pair' x y) ->
      (<>) <$> rec a x <*> rec b y
    (OSL.Product {}, _) -> typeMismatch
    (OSL.Coproduct _ a b, OSL.Iota1' x) ->
      mconcat <$> sequence
        [ pure [scalarValue zero],
          rec a x,
          defaultSigma11Values c b
        ]
    (OSL.Coproduct _ a b, OSL.Iota2' x) ->
      mconcat <$> sequence
        [ pure [scalarValue one],
          defaultSigma11Values c a,
          rec b x
        ]
    (OSL.Coproduct {}, _) -> typeMismatch
    (OSL.F _ _ a (OSL.N ann), f) ->
      scalarFunction a (OSL.N ann) f
    (OSL.F _ _ a (OSL.Z ann), f) ->
      scalarFunction a (OSL.Z ann) f
    (OSL.F _ _ a (OSL.Fin n ann), f) ->
      scalarFunction a (OSL.Fin n ann) f
    (OSL.F _ _ a (OSL.Fp ann), f) ->
      scalarFunction a (OSL.Fp ann) f
    (OSL.F ann n a (OSL.Product _ b d), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a b) . OSL.Fun =<< mapM OSL.fstOfPair f,
          rec (OSL.F ann n a d) . OSL.Fun =<< mapM OSL.sndOfPair f
        ]
    (OSL.F _ _ _ (OSL.Product {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.Coproduct _ b d), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) . OSL.Nat <$> iotaIndex y
              | (x, y) <- Map.toList f
              ],
          rec (OSL.F ann n a b) . OSL.Fun . Map.fromList . catMaybes $
            [ case y of
                OSL.Iota1' y' -> pure (x, y')
                _ -> Nothing
            | (x,y) <- Map.toList f
            ],
          rec (OSL.F ann n a d) . OSL.Fun . Map.fromList . catMaybes $
            [ case y of
                OSL.Iota2' y' -> pure (x, y')
                _ -> Nothing
            | (x,y) <- Map.toList f
            ]
        ]
    (OSL.F _ _ _ (OSL.Coproduct {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.Maybe _ b), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) . OSL.Nat <$> maybeIndex y
              | (x,y) <- Map.toList f
              ],
          do rec (OSL.F ann n a b) . OSL.Fun . Map.fromList
               =<< sequence
                 [ case y of
                     OSL.Maybe'' (Just y') -> pure (x, y')
                     OSL.Maybe'' Nothing -> (x,) <$> OSL.defaultValue c b
                     _ -> Left (ErrorMessage () "expected a maybe value")
                 | (x, y) <- Map.toList f
                 ]
        ]
    (OSL.F _ _ _ (OSL.Maybe {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.NamedType _ name), OSL.Fun f) ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data b) ->
          rec (OSL.F ann n a (OSL.dropTypeAnnotations b)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> fromTo y
              | (x,y) <- Map.toList f
              ]
        _ -> Left . ErrorMessage () $ "expected the name of a type"
    (OSL.F _ _ _ (OSL.NamedType {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.List _ m b), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> OSL.Nat <$> listLength y
              | (x,y) <- Map.toList f
              ],
          rec (OSL.F ann n a (OSL.F ann (Just m) (OSL.N ann) b)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> listElems y
              | (x,y) <- Map.toList f
              ]
        ]
    (OSL.F _ _ _ (OSL.List {}), _) -> typeMismatch
    (OSL.F ann n a (OSL.Map _ m b d), OSL.Fun f) ->
      mconcat <$> sequence
        [ rec (OSL.F ann n a (OSL.N ann)) . OSL.Fun . Map.fromList
            =<< sequence
              [ (x,) <$> OSL.Nat <$> mapSize y
              | (x,y) <- Map.toList f
              ],
          rec (OSL.F ann n a (OSL.F ann (Just m) (OSL.N ann) b)) . OSL.Fun . Map.fromList
            =<< sequence
              [ do ks <- mapKeys g
                   (x,) . OSL.Fun . Map.fromList <$> sequence
                     [ (,y) . OSL.Nat <$> fromInt i
                     | (i,y) <- zip [0..] ks
                     ]
              | (x,g) <- Map.toList f
              ],
          rec (OSL.F ann n a (OSL.F ann (Just m) b d)) (OSL.Fun f)
        ]
    (OSL.F _ _ _ (OSL.Map {}), _) -> typeMismatch
    (OSL.F ann _ a (OSL.F _ m b d), OSL.Fun f) -> do
      xs <- Map.fromList <$> sequence
        [(x,) <$> (toScalars =<< rec a x) | x <- Map.keys f]
      fs <- mapM (rec (OSL.F ann m b d)) f
      case Map.toList fs of
        (fs0:_) ->
          pure 
            [ S11.Value . Map.fromList $
              [ (x' <> y, z)
              | (x',fs') <- Map.elems (Map.intersectionWith (,) xs fs),
                (y,z) <- Map.toList . (^. #unValue) $ fromMaybe mempty (fs' `atMay` i)
              ]
            | i <- [0 .. length fs0 - 1]
            ]
        _ -> pure mempty
    (OSL.F _ _ _ (OSL.F {}), _) -> typeMismatch
    (OSL.F _ _ _ (OSL.P {}), _) ->
      Left . ErrorMessage () $ "unsupported: family of permutations"
    (OSL.F _ _ _ (OSL.Prop _), _) ->
      Left . ErrorMessage () $ "unsupported: Prop in function codomain"
    (OSL.P _ _ a b, f) ->
      scalarFunction a b f
    (OSL.Prop _, OSL.Bool x) -> pure [scalarValue (S11.boolToScalar x)]
    (OSL.Prop _, _) -> typeMismatch
    (OSL.Maybe _ a, OSL.Maybe'' Nothing) ->
      mconcat <$> sequence
        [ pure [scalarValue zero],
          defaultSigma11Values c a
        ]
    (OSL.Maybe _ a, OSL.Maybe'' (Just x)) ->
      mconcat <$> sequence
        [ pure [scalarValue one],
          rec a x
        ]
    (OSL.Maybe {}, _) -> typeMismatch
    (OSL.NamedType _ name, OSL.To' _ x) ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data a) -> rec (OSL.dropTypeAnnotations a) x
        _ -> Left . ErrorMessage () $ "expected the name of a type"
    (OSL.NamedType {}, _) -> typeMismatch
    (OSL.List ann n a, OSL.List'' xs) -> do
      mconcat <$> sequence
        [ (:[]) . scalarValue <$> fromInt (length xs),
          rec (OSL.F ann (Just n) (OSL.N ann) a)
            . OSL.Fun . Map.fromList =<< sequence
            [ (,x) <$> (OSL.Nat <$> fromInt i)
            | (i, x) <- zip [0..] xs
            ]
        ]
    (OSL.List {}, _) -> typeMismatch
    (OSL.Map ann n a b, OSL.Map'' xs) -> do
      mconcat <$> sequence
        [ (:[]) . scalarValue <$> fromInt (Map.size xs),
          rec (OSL.F ann (Just n) (OSL.N ann) a)
            . OSL.Fun . Map.fromList =<< sequence
            [ (,x) <$> (OSL.Nat <$> fromInt i)
            | (i, x) <- zip [0..] (Map.keys xs)
            ],
          rec (OSL.F ann (Just n) a b)
            (OSL.Fun xs)
        ]
    (OSL.Map {}, _) -> typeMismatch
  where
    scalarFunction a b (OSL.Fun f) =
      (:[]) . S11.Value . Map.fromList <$> sequence
        [ (,) <$> (toScalars =<< rec a x) <*> (toScalar =<< rec b y)
        | (x,y) <- Map.toList f
        ]
    scalarFunction _ _ _ = typeMismatch

    rec = toSigma11Values c

    iotaIndex :: OSL.Value -> Either (ErrorMessage ()) Scalar
    iotaIndex =
      \case
        OSL.Iota1' _ -> pure zero
        OSL.Iota2' _ -> pure one
        _ -> Left (ErrorMessage () "expected a coproduct value")

    maybeIndex :: OSL.Value -> Either (ErrorMessage ()) Scalar
    maybeIndex =
      \case
        OSL.Maybe'' Nothing -> pure zero
        OSL.Maybe'' (Just _) -> pure one
        _ -> Left (ErrorMessage () "expected a maybe value")

    listLength :: OSL.Value -> Either (ErrorMessage ()) Scalar
    listLength =
      \case
        OSL.List'' xs -> fromInt (length xs)
        _ -> Left (ErrorMessage () "expected a list")

    listElems :: OSL.Value -> Either (ErrorMessage ()) OSL.Value
    listElems =
      \case
        OSL.List'' xs ->
          OSL.Fun . Map.fromList <$> sequence
            [ (,x) . OSL.Nat <$> fromInt i
            | (i,x) <- zip [0..] xs
            ]
        _ -> Left (ErrorMessage () "expected a list")

    mapSize :: OSL.Value -> Either (ErrorMessage ()) Scalar
    mapSize =
      \case
        OSL.Map'' xs -> fromInt (Map.size xs)
        _ -> Left (ErrorMessage () "expected a map")

    mapKeys :: OSL.Value -> Either (ErrorMessage ()) [OSL.Value]
    mapKeys =
      \case
        OSL.Map'' xs -> pure (Map.keys xs)
        _ -> Left (ErrorMessage () "expected a map")

    fromTo :: OSL.Value -> Either (ErrorMessage ()) OSL.Value
    fromTo =
      \case
        OSL.To' _ x -> pure x
        _ -> Left (ErrorMessage () "expected a To value")


typeMismatch :: Either (ErrorMessage ()) a
typeMismatch = Left . ErrorMessage () $ "type mismatch"

fromInt :: Int -> Either (ErrorMessage ()) Scalar
fromInt x =
  maybe (Left (ErrorMessage () "int out of range of scalar field"))
    pure (integerToScalar (intToInteger x))

toScalars :: [S11.Value] -> Either (ErrorMessage ()) [Scalar]
toScalars = mapM (toScalar . (:[]))

toScalar :: [S11.Value] -> Either (ErrorMessage ()) Scalar
toScalar [S11.Value u] =
  case Map.lookup [] u of
    Just u' -> pure u'
    Nothing -> Left . ErrorMessage () $ "expected a scalar"
toScalar _ = Left . ErrorMessage () $ "expected a scalar"

defaultSigma11Values ::
  OSL.ValidContext t ann ->
  OSL.Type () ->
  Either (ErrorMessage ()) [S11.Value]
defaultSigma11Values c =
  \case
    OSL.NamedType _ name ->
      case Map.lookup name (c ^. #unValidContext) of
        Just (OSL.Data a) -> rec (OSL.dropTypeAnnotations a)
        _ -> Left (ErrorMessage () "expected the name of a type")
    OSL.Prop _ -> pure scalarDefault
    OSL.N _ -> pure scalarDefault
    OSL.Z _ -> pure scalarDefault
    OSL.Fp _ -> pure scalarDefault
    OSL.Fin {} -> pure scalarDefault
    OSL.F _ _ _ (OSL.P {}) ->
      Left (ErrorMessage () "unsupported: families of permutations")
    OSL.F _ _ _ (OSL.Prop _) ->
      Left (ErrorMessage () "unsupported: Prop in function codomain")
    OSL.F _ _ _ t ->
      fmap (const (S11.Value mempty)) <$> rec t
    OSL.P {} -> pure [S11.Value mempty]
    OSL.Product _ a b ->
      (<>) <$> rec a <*> rec b
    OSL.Coproduct _ a b ->
      mconcat <$> sequence
        [ pure scalarDefault,
          rec a,
          rec b
        ]
    OSL.Maybe _ a ->
      (scalarDefault <>) <$> rec a
    OSL.List ann n a ->
      (scalarDefault <>) <$> rec (OSL.F ann (Just n) (OSL.N ann) a)
    OSL.Map ann n a b ->
      mconcat <$> sequence
        [ pure scalarDefault,
          rec (OSL.F ann (Just n) (OSL.N ann) a),
          rec (OSL.F ann (Just n) a b)
        ]
  where
    rec = defaultSigma11Values c

    scalarDefault = [S11.Value (Map.singleton [] zero)]
