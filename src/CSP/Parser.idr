||| Parser for the binary CSP files found in `test`.
module CSP.Parser

import Text.Parser

import Data.String

import CSP.Lexer

%default total

public export
data CSPPart : Type where
  ||| The number of variables in a CSP.
  NVars : (n : Nat) -> CSPPart

  ||| Domain of a variable; lower and upper inclusive bound.
  Domain : (lBound : Nat) -> (uBound : Nat) -> CSPPart

  ||| Start of a constraint declaration between two variables.
  CStart : (idxA : Nat) -> (idxB : Nat) -> CSPPart

  ||| A tuple of permitted values.
  BinTup : (valA : Nat) -> (valB : Nat) -> CSPPart


||| For handling whitespace.
ws : Grammar _ CSPTok True ()
ws = terminal "Expected whitespace"
        (\case WS => pure ()
               _  => Nothing)

||| The number of variables. This should be the first thing in the CSP file.
nVars : Grammar _ CSPTok True CSPPart
nVars = termNVars
     <|> (do ignore $ some ws; termNVars)
     where
       termNVars : Grammar _ CSPTok True CSPPart
       termNVars = terminal "Expected nVars: a positive integer."
                      (\case (Val v) => do n <- parsePositive v; pure (NVars n)
                             _ => Nothing)

