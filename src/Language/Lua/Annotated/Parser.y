{
module Language.Lua.Annotated.Parser
  ( parseTokens
  , parseText
  , parseNamedText
  , parseFile
  , Parser
  , chunk
  , exp
  , stat
  , SourcePos(..)
  , SourceRange(..)
  ) where

import           Control.Monad (liftM,ap)
import           Prelude hiding (LT,GT,EQ,exp)
import           Data.Maybe(fromMaybe)
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text

import           Language.Lua.Token (Token(..))
import           Language.Lua.Annotated.Lexer
                    (SourcePos(..), SourceRange(..), Lexeme(..), llexNamed)
import           Language.Lua.Annotated.Syntax
import qualified AlexTools

}

%tokentype    { Lexeme Token }
%token
'+'           { Lexeme { lexemeToken = TokPlus      } }
'-'           { Lexeme { lexemeToken = TokMinus     } }
'*'           { Lexeme { lexemeToken = TokStar      } }
'/'           { Lexeme { lexemeToken = TokSlash     } }
'//'          { Lexeme { lexemeToken = TokDSlash    } }
'%'           { Lexeme { lexemeToken = TokPercent   } }
'^'           { Lexeme { lexemeToken = TokExp       } }
'#'           { Lexeme { lexemeToken = TokSh        } }
'=='          { Lexeme { lexemeToken = TokEqual     } }
'~='          { Lexeme { lexemeToken = TokNotequal  } }
'<='          { Lexeme { lexemeToken = TokLEq       } }
'>='          { Lexeme { lexemeToken = TokGEq       } }
'<'           { Lexeme { lexemeToken = TokLT        } }
'>'           { Lexeme { lexemeToken = TokGT        } }
'&'           { Lexeme { lexemeToken = TokAmpersand } }
'~'           { Lexeme { lexemeToken = TokTilde     } }
'|'           { Lexeme { lexemeToken = TokPipe      } }
'>>'          { Lexeme { lexemeToken = TokDGT       } }
'<<'          { Lexeme { lexemeToken = TokDLT       } }
'='           { Lexeme { lexemeToken = TokAssign    } }
'('           { Lexeme { lexemeToken = TokLParen    } }
')'           { Lexeme { lexemeToken = TokRParen    } }
'{'           { Lexeme { lexemeToken = TokLBrace    } }
'}'           { Lexeme { lexemeToken = TokRBrace    } }
'['           { Lexeme { lexemeToken = TokLBracket  } }
']'           { Lexeme { lexemeToken = TokRBracket  } }
'::'          { Lexeme { lexemeToken = TokDColon    } }
';'           { Lexeme { lexemeToken = TokSemic     } }
':'           { Lexeme { lexemeToken = TokColon     } }
','           { Lexeme { lexemeToken = TokComma     } }
'.'           { Lexeme { lexemeToken = TokDot       } }
'..'          { Lexeme { lexemeToken = TokDDot      } }
'...'         { Lexeme { lexemeToken = TokEllipsis  } }
'and'         { Lexeme { lexemeToken = TokAnd       } }
'break'       { Lexeme { lexemeToken = TokBreak     } }
'do'          { Lexeme { lexemeToken = TokDo        } }
'else'        { Lexeme { lexemeToken = TokElse      } }
'elseif'      { Lexeme { lexemeToken = TokElseIf    } }
'end'         { Lexeme { lexemeToken = TokEnd       } }
'false'       { Lexeme { lexemeToken = TokFalse     } }
'for'         { Lexeme { lexemeToken = TokFor       } }
'function'    { Lexeme { lexemeToken = TokFunction  } }
'goto'        { Lexeme { lexemeToken = TokGoto      } }
'if'          { Lexeme { lexemeToken = TokIf        } }
'in'          { Lexeme { lexemeToken = TokIn        } }
'local'       { Lexeme { lexemeToken = TokLocal     } }
'nil'         { Lexeme { lexemeToken = TokNil       } }
'not'         { Lexeme { lexemeToken = TokNot       } }
'or'          { Lexeme { lexemeToken = TokOr        } }
'repeat'      { Lexeme { lexemeToken = TokRepeat    } }
'return'      { Lexeme { lexemeToken = TokReturn    } }
'then'        { Lexeme { lexemeToken = TokThen      } }
'true'        { Lexeme { lexemeToken = TokTrue      } }
'until'       { Lexeme { lexemeToken = TokUntil     } }
'while'       { Lexeme { lexemeToken = TokWhile     } }
integer       { Lexeme { lexemeToken = TokInt       } }
float         { Lexeme { lexemeToken = TokFloat     } }
literalString { Lexeme { lexemeToken = TokSLit      } }
ident         { Lexeme { lexemeToken = TokIdent     } }

%monad { Either (SourceRange, String) }
%error { errorP }

-- local a=b(nil)() is one statement
-- local a=b;(nil)() is two statements
-- therefore EXP '('
-- f()(nil)() is one statement
-- f();(nil)() is two statements
-- therefore STAT PREFIX
%nonassoc STAT    EXP
%nonassoc PREFIX  '('

%left 'or'
%left 'and'
%left '<' '<=' '>' '>=' '==' '~='
%left '|'
%left '~'
%left '&'
%left '<<' '>>'
%right '..'
%left '+' '-'
%left '*' '/' '//' '%'
%nonassoc 'not' '#' NEG COMPLEMENT
%right '^'

%name chunk_ block
%name exp_ exp
%name stat_ stat

%%

opt(p)
  : p { Just $1 }
  |   { Nothing }

many   (p) : revMany(p)   { reverse $1 }
revMany(p) : revMany(p) p { $2 : $1    }
           |              { []         }

sepBy    (p,sep) : sepBy1(p,sep)          { $1         }
                 |                        { []         }
sepBy1   (p,sep) : revSepBy1(p,sep)       { reverse $1 }
revSepBy1(p,sep) : p                      { [$1]       }
                 | revSepBy1(p,sep) sep p { $3 : $1    }

block ::                    { Block SourceRange      }
  : many(stat) opt(retstat) { at ($1,$2) Block $1 $2 }

retstat ::                           { [Exp SourceRange] }
  : 'return' sepBy(exp,',') opt(';') { $2                }

stat ::                                                   { Stat SourceRange                  }
  : ';'                                                   { at $1 EmptyStat                   }
  | varlist '=' explist                                   { at (head $1,last $3) Assign $1 $3 }
  | functioncall %prec STAT                               { at $1 FunCall $1                  }
  | '::' name '::'                                        { at ($1,$3) Label $2               }
  | 'break'                                               { at $1 Break                       }
  | 'goto' name                                           { at ($1,$2) Goto $2                }
  | 'local' attnamelist opt(assign)                       { at ($1,($2,$3)) LocalAssign $2 $3 }

  ------- block structures -------------------------------
  | 'function' funcname funcbody 'end'                    { at ($1,$4)  FunAssign $2 $3         }
  | 'local' 'function' name funcbody 'end'                { at ($1,$5)  LocalFunAssign $3 $4    }
  | 'repeat' block 'until' exp                            { at ($1,$4)  Repeat $2 $4            }
  | 'do' block 'end'                                      { at ($1,$3)  Do $2                   }
  | 'while' exp 'do' block 'end'                          { at ($1,$5)  While $2 $4             }
  | 'if' exp 'then' block many(elseif) opt(else) 'end'    { at ($1,$7)  If (($2,$4):$5) $6      }
  | 'for' name '=' exp ',' exp opt(step) 'do' block 'end' { at ($1,$10) ForRange $2 $4 $6 $7 $9 }
  | 'for' namelist 'in' explist 'do' block 'end'          { at ($1,$7)  ForIn $2 $4 $6          }

  ------- error cases for block structures ---------------
  | 'function' funcname funcbody error                    {% noEndP $1 }
  | 'local' 'function' name funcbody error                {% noEndP $1 }
  | 'repeat' block error                                  {% noEndP $1 }
  | 'do' block error                                      {% noEndP $1 }
  | 'while' exp 'do' block error                          {% noEndP $1 }
  | 'if' exp 'then' block many(elseif) opt(else) error    {% noEndP $1 }
  | 'for' name '=' exp ',' exp opt(step) 'do' block error {% noEndP $1 }
  | 'for' namelist 'in' explist 'do' block error          {% noEndP $1 }

elseif : 'elseif' exp 'then' block { ($2,$4) }
else   : 'else' block { $2 }
step   : ',' exp { $2 }
assign : '=' explist { $2 }

varlist     : sepBy1(var,     ',') { $1 }
explist     : sepBy1(exp,     ',') { $1 }
namelist    : sepBy1(name,    ',') { $1 }
attnamelist : sepBy1(attname, ',') { $1 }

attname ::                    { (Name SourceRange, Maybe (Attrib SourceRange)) }
  : name                      { ($1, Nothing)                                  }
  | name '<' name '>'         {% attrname $1 $3                                }

prefixexp ::                  { PrefixExp SourceRange }
  : var                       { at $1 PEVar $1        }
  | functioncall %prec PREFIX { at $1 PEFunCall $1    }
  | '(' exp ')'               { at ($1,$3) Paren $2   }

functioncall ::               { FunCall SourceRange       }
  : prefixexp            args { at ($1,$2) NormalFunCall $1 $2 }
  | prefixexp methodname args { at ($1,$3) MethodCall $1 $2 $3 }

funcname ::                               { FunName SourceRange              }
  : name many(dottedname) opt(methodname) { at ($1,($2,$3)) FunName $1 $2 $3 }

dottedname : '.' name  { $2 }
methodname : ':' name  { $2 }

var ::                    { Var SourceRange               }
  : name                  { at $1 VarName $1              }
  | prefixexp '[' exp ']' { at ($1,$4) Select $1 $3       }
  | prefixexp '.' name    { at ($1,$3) SelectName $1 $3   }

exp ::                     { Exp SourceRange              }
  : 'nil'                  { at $1 Nil                    }
  | 'false'                { at $1 Bool False             }
  | 'true'                 { at $1 Bool True              }
  | integer                { at $1 Number IntNum (lexemeText $1) }
  | float                  { at $1 Number FloatNum (lexemeText $1) }
  | literalString          { at $1 String (lexemeText $1) }
  | '...'                  { at $1 Vararg                 }
  | functiondef            { at $1 EFunDef $1             }
  | prefixexp %prec EXP    { at $1 PrefixExp $1           }
  | tableconstructor       { at $1 TableConst $1          }

  | exp '+' exp   { at ($1,$3) Binop (at $2 Add   ) $1 $3 }
  | exp '-' exp   { at ($1,$3) Binop (at $2 Sub   ) $1 $3 }
  | exp '*' exp   { at ($1,$3) Binop (at $2 Mul   ) $1 $3 }
  | exp '/' exp   { at ($1,$3) Binop (at $2 Div   ) $1 $3 }
  | exp '//' exp  { at ($1,$3) Binop (at $2 IDiv  ) $1 $3 }
  | exp '^' exp   { at ($1,$3) Binop (at $2 Exp   ) $1 $3 }
  | exp '%' exp   { at ($1,$3) Binop (at $2 Mod   ) $1 $3 }
  | exp '..' exp  { at ($1,$3) Binop (at $2 Concat) $1 $3 }
  | exp '<'  exp  { at ($1,$3) Binop (at $2 LT    ) $1 $3 }
  | exp '<=' exp  { at ($1,$3) Binop (at $2 LTE   ) $1 $3 }
  | exp '>'  exp  { at ($1,$3) Binop (at $2 GT    ) $1 $3 }
  | exp '>=' exp  { at ($1,$3) Binop (at $2 GTE   ) $1 $3 }
  | exp '==' exp  { at ($1,$3) Binop (at $2 EQ    ) $1 $3 }
  | exp '~=' exp  { at ($1,$3) Binop (at $2 NEQ   ) $1 $3 }
  | exp 'and' exp { at ($1,$3) Binop (at $2 And   ) $1 $3 }
  | exp 'or'  exp { at ($1,$3) Binop (at $2 Or    ) $1 $3 }
  | exp '&' exp   { at ($1,$3) Binop (at $2 BAnd  ) $1 $3 }
  | exp '|' exp   { at ($1,$3) Binop (at $2 BOr   ) $1 $3 }
  | exp '~' exp   { at ($1,$3) Binop (at $2 BXor  ) $1 $3 }
  | exp '<<' exp  { at ($1,$3) Binop (at $2 ShiftL) $1 $3 }
  | exp '>>' exp  { at ($1,$3) Binop (at $2 ShiftR) $1 $3 }

  | '-' exp %prec NEG        { at ($1,$2) Unop (at $1 Neg)        $2 }
  | '~' exp %prec COMPLEMENT { at ($1,$2) Unop (at $1 Complement) $2 }
  | 'not' exp                { at ($1,$2) Unop (at $1 Not)        $2 }
  | '#'  exp                 { at ($1,$2) Unop (at $1 Len)        $2 }

args ::                    { FunArg SourceRange              }
  : '(' sepBy(exp,',') ')' { at ($1,$3) Args $2              }
  | tableconstructor       { at $1 TableArg $1               }
  | literalString          { at $1 StringArg (lexemeText $1) }

functiondef ::                { FunDef SourceRange    }
  : 'function' funcbody 'end' { at ($1,$3) FunDef $2  }
  | 'function' funcbody error {% noEndP $1            }

funcbody ::               { FunBody SourceRange                     }
  : '(' parlist ')' block { at ($1,$4) FunBody (fst $2) (snd $2) $4 }

parlist ::              { ([Name SourceRange],Maybe SourceRange) }
  : parnames1 ',' '...' { (reverse $1,getRange $3)               }
  | parnames1           { (reverse $1,Nothing)                   }
  | '...'               { ([], getRange $1)                      }
  |                     { ([], Nothing)                          }

parnames1 ::           { [Name SourceRange] }
  : name               { [$1]               }
  | parnames1 ',' name { $3 : $1            }

tableconstructor ::                 { Table SourceRange             }
  : '{'                         '}' { at ($1,$2) Table []           }
  | '{' fieldlist opt(fieldsep) '}' { at ($1,$3) Table (reverse $2) }

fieldlist ::                  { [TableField SourceRange] }
  : fieldlist fieldsep field  { $3 : $1                  }
  | field                     { [$1]                     }

fieldsep :: { Lexeme Token }
  : ','     { $1 }
  | ';'     { $1 }

field ::                { TableField SourceRange      }
  : '[' exp ']' '=' exp { at ($1,$5) ExpField $2 $5   }
  | name        '=' exp { at ($1,$3) NamedField $1 $3 }
  |                 exp { at $1      Field $1         }

name ::   { Name SourceRange           }
  : ident { at $1 Name (lexemeText $1) }

{

newtype Parser a = Parser ([Lexeme Token] -> Either (SourceRange,String) a)

-- | Parse a stream of tokens.
parseTokens :: Parser a -> [Lexeme Token] -> Either (SourceRange,String) a
parseTokens (Parser p) = p

chunk :: Parser (Block SourceRange)
chunk = Parser chunk_

stat :: Parser (Stat SourceRange)
stat = Parser stat_

exp :: Parser (Exp SourceRange)
exp = Parser exp_

instance Functor Parser where
  fmap f (Parser p) = Parser (fmap (fmap f) p)

errorP :: [Lexeme Token] -> Either (SourceRange,String) a
errorP ts =
  case ts of
    [] -> Left (fakeRng, "unexpected end of file")
      where fake = SourcePos (-1)(-1)(-1) (Text.pack "(fake pos)")
            fakeRng = SourceRange fake fake
    Lexeme { lexemeRange = rng, lexemeToken = t }:_ ->
      Left (rng, "unexpected " ++ show t)

noEndP :: Lexeme Token -> Either (SourceRange,String) a
noEndP Lexeme { lexemeRange = pos, lexemeToken = t } =
  Left (pos, "unterminated " ++ show t)

attrname :: Name a -> Name a -> Either (a,String) (Name a, Maybe (Attrib a))
attrname x (Name a y)
  | y == Text.pack "close" = Right (x, Just (AttribClose a))
  | y == Text.pack "const" = Right (x, Just (AttribConst a))
  | otherwise              = Left  (a, "unknown attribute")

-- | Runs Lua lexer before parsing. Use @parseNamedText stat "name"@ to parse
-- statements, and @parseText exp "name"@ to parse expressions.
parseNamedText ::
  Parser a ->
  String {- ^ name -} ->
  Text {- ^ chunk -} ->
  Either (SourceRange, String) a
parseNamedText p n xs = parseTokens p (llexNamed n xs)

-- | Runs Lua lexer before parsing. Use @parseText stat@ to parse
-- statements, and @parseText exp@ to parse expressions.
parseText ::
  Parser a ->
  Text {- ^ chunk -} ->
  Either (SourceRange, String) a
parseText p = parseNamedText p "=<string>"

-- | Parse a Lua file. You can use @parseText chunk@ to parse a file from a string.
parseFile :: FilePath -> IO (Either (SourceRange, String) (Block SourceRange))
parseFile fp = fmap (parseNamedText chunk fp) (Text.readFile fp)



--------------------------------------------------------------------------------

at :: HasRange a => a -> (SourceRange -> b) -> b
at rng mk = mk $ fromMaybe fake $ getRange rng
  where
  none = SourcePos 0 1 1 (Text.pack "(nowehere)")
  fake = SourceRange { sourceFrom = none, sourceTo = none }

class HasRange a where
  getRange :: a -> Maybe SourceRange

instance HasRange SourceRange where
  getRange = Just

instance HasRange (Lexeme a) where
  getRange = Just . AlexTools.range

instance HasRange a => HasRange (Maybe a) where
  getRange x = getRange =<< x

instance (HasRange a, HasRange b) => HasRange (a,b) where
  getRange (x,y) =
    case (getRange x, getRange y) of
      (Nothing,Nothing) -> Nothing
      (Just a, Nothing) -> Just a
      (Nothing, Just a) -> Just a
      (Just a, Just b)  ->
        Just $! SourceRange { sourceFrom = sourceFrom a, sourceTo = sourceTo b }

instance HasRange a => HasRange [a] where
  getRange (x : xs) = getRange (x,xs)
  getRange []       = Nothing

instance HasRange a => HasRange (Stat  a)       where getRange = getRange . ann
instance HasRange a => HasRange (Exp   a)       where getRange = getRange . ann
instance HasRange a => HasRange (Var   a)       where getRange = getRange . ann
instance HasRange a => HasRange (Binop a)       where getRange = getRange . ann
instance HasRange a => HasRange (Unop  a)       where getRange = getRange . ann
instance HasRange a => HasRange (PrefixExp a)   where getRange = getRange . ann
instance HasRange a => HasRange (Table a)       where getRange = getRange . ann
instance HasRange a => HasRange (TableField a)  where getRange = getRange . ann
instance HasRange a => HasRange (Block a     )  where getRange = getRange . ann
instance HasRange a => HasRange (FunName a)     where getRange = getRange . ann
instance HasRange a => HasRange (FunDef a)      where getRange = getRange . ann
instance HasRange a => HasRange (FunBody a)     where getRange = getRange . ann
instance HasRange a => HasRange (FunCall a)     where getRange = getRange . ann
instance HasRange a => HasRange (FunArg a)      where getRange = getRange . ann
instance HasRange a => HasRange (Name a)        where getRange = getRange . ann
instance HasRange a => HasRange (Attrib a)      where getRange = getRange . ann

}
