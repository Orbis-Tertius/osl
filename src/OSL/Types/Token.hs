module OSL.Types.Token (Token (..)) where


import OSL.Types.Keyword (Keyword (..))
import OSL.Types.OSL (Name (..))


data Token = Var Name | Keyword Keyword | ThinArrow | Colon
  | OpenParen | CloseParen | ConstN Integer | ConstZ Integer | ConstFin Integer
  | ProductOp | Comma | CoproductOp | AddNOp | MulNOp | AddZOp | MulZOp
  | Equals | LessOrEquals | And | Or | Not | ForAll | ForSome
  | Lambda | ThickArrow | Congruent | DefEquals | Semicolon | Period
