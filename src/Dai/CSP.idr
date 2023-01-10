module Dai.CSP

import System.File

import Dai.CSP.Lexer

import public Text.Parser
import public Dai.CSP.Parser

||| Attempt to parse the contents of the given file as a CSP definition,
||| returning an error message if something went wrong.
export
parseFile : File -> IO (Either String CSP)
parseFile fh =
  do Right contents <- fRead fh
       | Left fErr => pure (Left $ "ERROR: " ++ show fErr)
     let (toks, (_, _, "")) = lex contents
       | (_, (_, _, rem)) => pure (Left $ lexError rem)
     let Right (theCSP, []) = parse toks
       | Right (_, rem) => pure (Left $ parseRemError rem)
       | Left errs => pure (Left $ parseError errs)
     pure (Right theCSP)
  where
    lexError : (rem : String) -> String
    lexError rem =
      """
      ERROR: Couldn't lex entire file! Remainder:
      -----
      \{rem}
      -----
      """

    parseRemError : (rem : List (WithBounds CSPTok)) -> String
    parseRemError rem =
      """
      ERROR: Couldn't parse entire token stream! Remainder:
      -----
      \{show rem}
      -----
      """

    parseError : (errs : List1 (ParsingError CSPTok)) -> String
    parseError errs =
      """
      ERROR: Error(s) while parsing token stream!:
      -----
      \{concatMap ((++) "\n") (map show errs)}
      -----
      """


