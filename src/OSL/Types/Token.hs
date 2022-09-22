module OSL.Types.Token (Token (..)) where


import OSL.Types.Keyword (Keyword (..))
import OSL.Types.OSL (Name (..))


data Token = Var Name | Keyword Keyword | ThinArrow | Colon
  | OpenParen | CloseParen | Const Integer | LeftRightArrow
  | ConstN Integer | ConstZ Integer | ConstFin Integer
  | ProductOp | Comma | CoproductOp | AddNOp | MulNOp | AddZOp | MulZOp
  | Equal | Less | LessOrEqual | And | Or | Not | ForAll | ForSome
  | Lambda | ThickArrow | Congruent | DefEquals | Semicolon | Period
  | Caret | OpenBracket | CloseBracket | OpenBrace | CloseBrace
  deriving (Eq, Show)
