||| Lexer for the binary CSP files found in `test`.
module CSP.Lexer

import Text.Lexer

import Deriving.Show
%language ElabReflection

%default total

public export
data CSPTok : Type where
  Comment : CSPTok
  LParens : CSPTok
  RParens : CSPTok
  Comma : CSPTok

  -- FIXME: separate into newlines and spaces, otherwise parser breaks
  ||| An amount of whitespace
  WS : CSPTok

  ||| Start of a constraint declaration
  CStart : CSPTok

  ||| A positive value (nVars, domain bound, or idx)
  Val : String -> CSPTok

public export
%hint
ShowCSPTok : Show CSPTok
ShowCSPTok = %runElab derive


||| Comments start with '//'.
cspComment : Lexer
cspComment = lineComment $ exact "//"

||| '(' -- for constraint declarations.
lParens : Lexer
lParens = is '('

||| ')' -- for constraint declarations.
rParens : Lexer
rParens = is ')'

||| ',' -- for comma-separated values.
comma : Lexer
comma = is ','

||| An amount of whitespace
ws : Lexer
ws = spaces

||| 'c' -- start of a constraint declaration
cStart : Lexer
cStart = is 'c'

||| A value is a single, positive integer.
val : Lexer
val = digits

||| A map from lexers to functions returning the correct tokens.
cspMap : TokenMap CSPTok
cspMap =
  [ (cspComment, const Comment)
  , (lParens   , const LParens)
  , (rParens   , const RParens)
  , (comma     , const Comma)
  , (ws        , const WS)
  , (cStart    , const CStart)
  , (val       , \v => Val v)
  ]


||| Relevant tokens is everything apart from comments.
relevant : WithBounds CSPTok -> Bool
relevant (MkBounded Comment _ _) = False
relevant _ = True

||| Remove the irrelevant tokens (i.e. comments).
clean :  (List (WithBounds CSPTok), (Int, (Int, String)))
      -> (List (WithBounds CSPTok), (Int, (Int, String)))
clean (tokens, inputRemainder) = (filter relevant tokens, inputRemainder)

||| Lex a string containing a CSP.
export
lex : String -> (List (WithBounds CSPTok), (Int, (Int, String)))
lex cspStr = clean $ lex cspMap cspStr

