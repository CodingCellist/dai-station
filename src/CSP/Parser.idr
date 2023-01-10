||| Parser for the binary CSP files found in `test`.
module CSP.Parser

import Text.Parser

import Data.List1
import Data.String
import System.File

import CSP.Lexer

%default total

||| The "head" of a constraint, containing the variable indices the constraint
||| concerns.
||| N.B.: Indexes start at 0.
public export
data CDecl : Type where
  CHead : (idxA : Nat) -> (idxB : Nat) -> CDecl

||| A binary tuple of values.
public export
data BinTup : Type where
  Tup : (valA : Nat) -> (valB : Nat) -> BinTup

  

||| The constituent parts of a CSP:
|||   - a number of variables
|||   - variable domains
|||   - constraints
public export
data CSPPart : Type where
  ||| The number of variables in a CSP.
  NVars : (n : Nat) -> CSPPart

  ||| Domain of a variable; lower and upper inclusive bound.
  Domain : (lBound : Nat) -> (uBound : Nat) -> CSPPart

  ||| There are 2 parts to a constraint:
  |||   1) The "head", containing the variable indices the constraint concerns.
  |||   2) The tuples of valid values that the variables may assume.
  Constraint : (cIdxs : CDecl) -> (tups : List1 BinTup) -> CSPPart


||| A Constraint Satisfaction Problem.
public export
data CSP : Type where
  MkCSP :  (noVars : CSPPart)
        -> (doms : List1 CSPPart)
        -> (cs : List CSPPart)    -- Nil is just "anything goes"
        -> CSP

||| Parse a single `LParens` token.
lParens : Grammar _ CSPTok True ()
lParens = terminal "Expected '('"
            (\case LParens => pure ()
                   _       => Nothing)

||| Parse a single `RParens` token.
rParens : Grammar _ CSPTok True ()
rParens = terminal "Expected ')'"
            (\case RParens => pure ()
                   _       => Nothing)

||| Parse a single `Comma` token.
comma : Grammar _ CSPTok True ()
comma = terminal "Expected a comma"
          (\case Comma => pure ()
                 _     => Nothing)

||| Parse a single `Space` token.
aSpace : Grammar _ CSPTok True ()
aSpace = terminal "Expected ' ' (a space)"
            (\case Space => pure ()
                   _     => Nothing)

||| Parse a single `Newline` token.
newline : Grammar _ CSPTok True ()
newline = terminal "Expected a newline/line-break"
            (\case Newline => pure ()
                   _       => Nothing)

||| A value which must be positive, i.e. a `Nat`.
natVal : Grammar _ CSPTok True Nat
natVal = terminal "Expected a positive integer"
            (\case (Val v) => do n <- parsePositive v ; pure n
                   _       => Nothing)

||| Parse the first token of a constraint declaration (`CStart`).
cStart : Grammar _ CSPTok True ()
cStart = terminal "Expected the start of a constraint (i.e. a 'c')"
            (\case CStart => pure ()
                   _      => Nothing)

||| The number of variables. This should be the first thing in the CSP file.
nVars : Grammar _ CSPTok True CSPPart
nVars =
  do n <- natVal
     newline
     pure (NVars n)

||| A domain is the lower bound, a comma, optionally some spaces, and then the
||| upper bound.
domain : Grammar _ CSPTok True CSPPart
domain =
  do lBound <- natVal
     comma
     uBound <- afterMany aSpace natVal
     newline
     pure (Domain lBound uBound)

||| The start of a constraint declaration is denoted by a 'c', a left
||| parenthesis, the index of the first variable, a comma, optionally some
||| spaces, the index of the second variable, and finally a right parenthesis.
cDecl : Grammar _ CSPTok True CDecl
cDecl =
  do cStart
     lParens
     idxA <- natVal
     comma
     idxB <- afterMany aSpace natVal
     rParens
     newline
     pure (CHead idxA idxB)

||| A binary tuple is the first value, a comma, optionally some spaces, and then
||| the second value.
%inline
binTup : Grammar _ CSPTok True BinTup
binTup =
  do valA <- natVal
     comma
     valB <- afterMany aSpace natVal
     newline
     pure (Tup valA valB)

||| A constraint is a declaration, followed by some binary tuples of values.
constraint : Grammar _ CSPTok True CSPPart
constraint =
  do decl <- cDecl
     tups <- some binTup
     newline
     pure (Constraint decl tups)

||| A Constraint Satisfaction Problem consists of the number of variables to
||| solve, the domains of the variables, and the constraints between them.
csp : Grammar _ CSPTok True CSP
csp =
  do noVars <- afterMany newline $ nVars
     doms   <- afterMany newline $ some domain
     cs     <- many $ afterMany newline constraint
     pure (MkCSP noVars doms cs)

||| Parse the given CSP token-stream.
export
parse : List (WithBounds CSPTok) -> Either (List1 (ParsingError CSPTok)) (CSP, List (WithBounds CSPTok))
parse toks = parse csp toks


%default partial

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

