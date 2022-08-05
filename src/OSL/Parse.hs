{-# LANGUAGE LambdaCase #-}


module OSL.Parse (parseContext) where


import Control.Monad (guard, mzero)
import Data.Either.Combinators (mapLeft)
import Data.Text (Text, pack, unpack)
import Text.Parsec (SourceName, SourcePos, Parsec, many, eof, token, (<|>), try, choice, getPosition, option, many1)
import qualified Text.Parsec.Prim as Prim

import OSL.Types.ErrorMessage (ErrorMessage (..))
import OSL.Types.OSL (Context (..), Name, Declaration (..), Term (..), Type (..))
import qualified OSL.Types.Keyword as K
import OSL.Types.Token (Token)
import qualified OSL.Types.Token as T


parseContext :: SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) (Context SourcePos)
parseContext = parse' context


type Parser = Parsec [(Token, SourcePos)] ()


parse' :: Parser a -> SourceName -> [(Token, SourcePos)] -> Either (ErrorMessage ()) a
parse' p n = mapLeft (ErrorMessage () . pack . show) . Prim.parse p n


consume :: ((Token, SourcePos) -> Maybe a) -> Parser a
consume = token (unpack . printToken . fst) snd


consumeExact :: Token -> (SourcePos -> a) -> Parser a
consumeExact tok tm =
  consume (\(t, p) -> guard (t == tok) >> return (tm p))


consumeExact_ :: Token -> Parser ()
consumeExact_ tok = consumeExact tok (const ())


printToken :: Token -> Text
printToken = pack . show


context :: Parser (Context SourcePos)
context = do
  decls <- many declaration
  eof
  return (Context decls)


declaration :: Parser (Name, Declaration SourcePos)
declaration =
  choice
  [ dataDeclaration
  , defDeclaration
  , freeDeclaration
  ]


dataDeclaration :: Parser (Name, Declaration SourcePos)
dataDeclaration = do
  consumeExact_ (T.Keyword K.Data)
  n <- name
  consumeExact_ T.Congruent
  t <- type0
  consumeExact_ T.Period
  return (n, Data t)


defDeclaration :: Parser (Name, Declaration SourcePos)
defDeclaration = do
  consumeExact_ (T.Keyword K.Def)
  n <- name
  consumeExact_ T.Colon
  ty <- type0
  consumeExact_ T.DefEquals
  def <- term0
  consumeExact_ T.Period
  return (n, Defined ty def)


freeDeclaration :: Parser (Name, Declaration SourcePos)
freeDeclaration = do
  n <- name
  consumeExact_ T.Colon
  t <- type0
  consumeExact_ T.Period
  return (n, FreeVariable t)


name :: Parser Name
name =
  consume $
    \case
      (T.Var x, _) -> pure x
      _            -> mzero


type0 :: Parser (Type SourcePos)
type0 = do
  p <- getPosition
  t <- type1
  ts <- option Nothing (consumeExact_ T.ThinArrow >> (Just <$> type0))
  case ts of
    Nothing -> return t
    Just t' -> return (F p t t')


type1 :: Parser (Type SourcePos)
type1 = do
  p <- getPosition
  t <- type2
  ts <- option Nothing ((Just. Left <$> productTail) <|> (Just . Right <$> coproductTail))
  case ts of
    Nothing -> return t
    Just (Left ts') -> return (Product p t ts')
    Just (Right ts') -> return (Coproduct p t ts')


productTail :: Parser (Type SourcePos)
productTail = do
  p <- getPosition
  consumeExact_ T.ProductOp
  t <- type2
  ts <- option Nothing (Just <$> productTail)
  case ts of
    Nothing -> return t
    Just ts' -> return (Product p t ts')


coproductTail :: Parser (Type SourcePos)
coproductTail = do
  p <- getPosition
  consumeExact_ T.CoproductOp
  t <- type2
  ts <- option Nothing (Just <$> coproductTail)
  case ts of
    Nothing -> return t
    Just ts' -> return (Coproduct p t ts')


type2 :: Parser (Type SourcePos)
type2 =
  choice
  $
  try
  <$>
  [ consumeExact (T.Keyword K.Prop) Prop
  , consumeExact (T.Keyword K.N) N
  , consumeExact (T.Keyword K.Z) Z
  , NamedType <$> getPosition <*> name
  , parenthesizedType
  , finiteType
  , maybeType
  , listType
  , mapType
  ]


parenthesizedType :: Parser (Type SourcePos)
parenthesizedType = do
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  return t


finiteType :: Parser (Type SourcePos)
finiteType = do
  consumeExact_ (T.Keyword K.Fin)
  consumeExact_ T.OpenParen
  t <- consume $
    \case
      (T.Const i, p) -> return (Fin p i)
      _ -> mzero
  consumeExact_ T.CloseParen
  return t


maybeType :: Parser (Type SourcePos)
maybeType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Maybe)
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  return (Maybe p t)


listType :: Parser (Type SourcePos)
listType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.List)
  consumeExact_ T.OpenParen
  t <- type0
  consumeExact_ T.CloseParen
  return (List p t)


mapType :: Parser (Type SourcePos)
mapType = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Map)
  consumeExact_ T.OpenParen
  t0 <- type0
  consumeExact_ T.Comma
  t1 <- type0
  consumeExact_ T.CloseParen
  return (Map p t0 t1)


term0 :: Parser (Term SourcePos)
term0 =
  choice
  $
  [ quantifier T.ForAll ForAll
  , quantifier T.ForSome ForSome
  , lambda
  , letExpr
  , term1
  ]


quantifier :: Token
  -> (SourcePos
      -> Name
      -> Type (SourcePos)
      -> Term (SourcePos)
      -> Term SourcePos)
  -> Parser (Term SourcePos)
quantifier tok ctor = do
  p <- getPosition
  consumeExact_ tok
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.Comma
  q <- term0
  return (ctor p varName varType q)


lambda :: Parser (Term SourcePos)
lambda = do
  p <- getPosition
  consumeExact_ T.Lambda
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.ThickArrow
  y <- term0
  return (Lambda p varName varType y)


letExpr :: Parser (Term SourcePos)
letExpr = do
  p <- getPosition
  consumeExact_ (T.Keyword K.Let)
  varName <- name
  consumeExact_ T.Colon
  varType <- type0
  consumeExact_ T.DefEquals
  def <- term0
  consumeExact_ T.Semicolon
  y <- term0
  return (Let p varName varType def y)


term1 :: Parser (Term SourcePos)
term1 = do
  x <- term2
  try (operatorOn x) <|> return x


operatorOn :: Term SourcePos -> Parser (Term SourcePos)
operatorOn x = do
  p <- getPosition
  op <- consume $
    \case
      (T.And, _) -> return T.And
      (T.Or, _) -> return T.Or
      (T.AddNOp, _) -> return T.AddNOp
      (T.MulNOp, _) -> return T.MulNOp
      (T.AddZOp, _) -> return T.AddZOp
      (T.MulZOp, _) -> return T.MulZOp
      (T.ProductOp, _) -> return T.ProductOp
      (T.CoproductOp, _) -> return T.CoproductOp
      (T.ThinArrow, _) -> return T.ThinArrow
      (T.Equal, _) -> return T.Equal
      (T.LessOrEqual, _) -> return T.LessOrEqual
      _ -> Nothing
  xs <-
    if isAssociative op
    then do
      y <- term2
      ys <- many (consumeExact_ op >> term2)
      return (y:ys)
    else (:[]) <$> term2
  return (foldl (opCtor op p) x xs)
  where
    opCtor =
      \case
        T.And -> And
        T.Or -> Or
        T.AddNOp -> applyBinaryOp AddN
        T.MulNOp -> applyBinaryOp MulN
        T.AddZOp -> applyBinaryOp AddZ
        T.MulZOp -> applyBinaryOp MulZ
        T.ProductOp -> FunctionProduct
        T.CoproductOp -> FunctionCoproduct
        T.ThinArrow -> Implies
        T.Equal -> Equal
        T.LessOrEqual -> LessOrEqual
        _ -> error "opCtor called outside defined domain"

    isAssociative =
      \case
        T.And -> True
        T.Or -> True
        T.AddNOp -> True
        T.MulNOp -> True
        T.AddZOp -> True
        T.MulZOp -> True
        T.ProductOp -> True
        T.CoproductOp -> True
        T.ThinArrow -> False
        T.Equal -> False
        T.LessOrEqual -> False
        _ -> error "isAssociative called outside defined domain"


term2 :: Parser (Term SourcePos)
term2 =
  choice
  $
  try
  <$>
  [ tuple
  , unaryOp term0 T.Not Not
  , functionApplication
  , term3
  ]


functionApplication :: Parser (Term SourcePos)
functionApplication = do
  p <- getPosition
  f <- term3
  consumeExact_ T.OpenParen
  arg <- term1
  args <- many (consumeExact_ T.Comma >> term1)
  consumeExact_ T.CloseParen
  return (foldl (Apply p) f (arg:args))


parenthesizedTerm :: Parser (Term SourcePos)
parenthesizedTerm = do
  consumeExact_ T.OpenParen
  x <- term0
  consumeExact_ T.CloseParen
  return x


term3 :: Parser (Term SourcePos)
term3 =
  choice
  $
  [ namedTerm
  , constant
  , parenthesizedTerm
  , builtin K.Cast Cast
  , builtin K.Pi1 Pi1
  , builtin K.Pi2 Pi2
  , builtin K.Iota1 Iota1
  , builtin K.Iota2 Iota2
  , unaryOp name (T.Keyword K.To) To
  , unaryOp name (T.Keyword K.From) From
  , builtin K.Nothing' Nothing'
  , builtin K.Just' Just'
  , unaryOp term0 (T.Keyword K.Maybe') Maybe'
  , builtin K.Exists Exists
  , builtin K.Length Length
  , builtin K.Nth Nth
  , functorApplication
  , builtin K.Lookup Lookup
  , builtin K.Keys Keys
  , builtin K.SumMapLength SumMapLength
  , unaryOp term0 (T.Keyword K.SumListLookup) SumListLookup
  ]


namedTerm :: Parser (Term SourcePos)
namedTerm = do
  p <- getPosition
  NamedTerm p <$> name


constant :: Parser (Term SourcePos)
constant =
  consume $
    \case
      (T.ConstN i, p) -> return (ConstN p i)
      (T.ConstZ i, p) -> return (ConstZ p i)
      (T.ConstFin i, p) -> return (ConstFin p i)
      _ -> Nothing


builtin :: K.Keyword
  -> (SourcePos -> Term SourcePos)
  -> Parser (Term SourcePos)
builtin k op = do
  p <- getPosition
  consumeExact_ (T.Keyword k)
  return (op p)


functorApplication :: Parser (Term SourcePos)
functorApplication = do
  (f, p) <- consume $
    \case
      (T.Keyword K.List, p) -> return (K.List, p)
      (T.Keyword K.Map, p) -> return (K.Map, p)
      _ -> Nothing
  case f of
    K.List -> do
      consumeExact_ T.OpenParen
      g <- consume $
        \case
          (T.Keyword K.Pi1, _) -> return K.Pi1
          (T.Keyword K.Pi2, _) -> return K.Pi2 
          (T.Keyword K.To, _) -> return K.To
          (T.Keyword K.From, _) -> return K.From
          (T.Keyword K.Length, _) -> return K.Length
          (T.Keyword K.Maybe, _) -> return K.Maybe
          _ -> Nothing
      h <- case g of
        K.Pi1 -> return (ListPi1 p)
        K.Pi2 -> return (ListPi2 p)
        K.To -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          return (ListTo p a)
        K.From -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          return (ListFrom p a)
        K.Length -> return (ListLength p)
        K.Maybe -> do
          consumeExact_ T.OpenParen
          i <- consume $
            \case
              (T.Keyword K.Pi1, _) -> return K.Pi1
              (T.Keyword K.Pi2, _) -> return K.Pi2
              (T.Keyword K.Length, _) -> return K.Length
              _ -> Nothing
          j <- case i of
            K.Pi1 -> return (ListMaybePi1 p)
            K.Pi2 -> return (ListMaybePi2 p)
            K.Length -> return (ListMaybeLength p)
            _ -> mzero
          consumeExact_ T.CloseParen
          return j
        _ -> mzero
      consumeExact_ T.CloseParen
      return h
    K.Map -> do
      consumeExact_ T.OpenParen
      g <- consume $
        \case
          (T.Keyword K.Pi1, _) -> return K.Pi1
          (T.Keyword K.Pi2, _) -> return K.Pi2
          (T.Keyword K.To, _) -> return K.To
          (T.Keyword K.From, _) -> return K.From
          _ -> Nothing
      h <- case g of
        K.Pi1 -> return (MapPi1 p)
        K.Pi2 -> return (MapPi2 p)
        K.To -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          return (MapTo p a)
        K.From -> do
          consumeExact_ T.OpenParen
          a <- name
          consumeExact_ T.CloseParen
          return (MapFrom p a)
        _ -> mzero
      consumeExact_ T.CloseParen
      return h
    _ -> mzero


applyBinaryOp :: (SourcePos -> Term SourcePos)
  -> SourcePos
  -> Term SourcePos
  -> Term SourcePos
  -> Term SourcePos
applyBinaryOp op p x y = Apply p (Apply p (op p) x) y


unaryOp :: Parser a
  -> Token
  -> (SourcePos -> a -> Term SourcePos)
  -> Parser (Term SourcePos)
unaryOp subexpr opTok opCtor = do
  p <- getPosition
  consumeExact_ opTok
  consumeExact_ T.OpenParen
  x <- subexpr
  consumeExact_ T.CloseParen
  return (opCtor p x)


tuple :: Parser (Term SourcePos)
tuple = do
  p <- getPosition
  consumeExact_ T.OpenParen
  x <- term1
  xs <- many1 (consumeExact_ T.Comma >> term1)
  consumeExact_ T.CloseParen
  return
    (foldl
      (\y z -> Apply p (Apply p (Pair p) y) z)
      x
      xs)
