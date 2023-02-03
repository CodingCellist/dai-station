{-
 - A constraint solver written in Idris2
 - Copyright (c) 2023, Thomas E. Hansen (CodingCellist)
 - SPDX-License-Identifier: BSD-3-Clause
 -}

||| Parser for the binary CSP files found in `test`.
module Dai.CSP.Parser

import Text.Parser

import Data.Vect
import Data.List1
import Data.String

import Dai.CSP.Lexer
import Dai.CSP.Common

%default total

||| Domain of a variable; lower and upper inclusive bound.
record Domain where
  constructor MkDomain
  lBound : Nat
  uBound : Nat

||| The "head" of a constraint, containing the variable indices the constraint
||| concerns.
||| N.B.: Indexes start at 0.
data CDecl : Type where
  CHead : (idxA : Nat) -> (idxB : Nat) -> CDecl

||| There are 2 parts to a constraint:
|||   1) The "head", containing the variable indices the constraint concerns.
|||   2) The tuples of valid values that the variables may assume.
data Constraint : Type where
  MkConstraint : (cIdxs : CDecl) -> (tups : List1 (Nat, Nat)) -> Constraint

||| Convert the given constraint to a pair of arcs.
||| (arcs are directional, constraints are not)
|||
||| The list of variables is required to copy the relevant variables into the
||| arcs.
export
constrToArcs : (vars : List Variable) -> Constraint -> (Arc, Arc)
constrToArcs vars (MkConstraint (CHead idxA idxB) tups) =
  let tups' = forget tups
      [varA] = filter (\v => v.idx == idxA) vars
        | [] => assert_total $ idris_crash "constrToArcs_no_varA_ERROR"
        | _  => assert_total $ idris_crash "constrToArcs_multivarA_ERROR"
      [varB] = filter (\v => v.idx == idxB) vars
        | [] => assert_total $ idris_crash "constrToArcs_no_varB_ERROR"
        | _  => assert_total $ idris_crash "constrToArcs_multivarB_ERROR"
      arc1 = MkArc varA varB tups'
      arc2 = MkArc varB varA (map swap tups')
  in (arc1, arc2)


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
nVars : Grammar _ CSPTok True Nat
nVars =
  do n <- natVal
     newline
     pure n

||| A domain is the lower bound, a comma, optionally some spaces, and then the
||| upper bound.
domain : Grammar _ CSPTok True Domain
domain =
  do lBound <- natVal
     comma
     uBound <- afterMany aSpace natVal
     newline
     pure (MkDomain lBound uBound)

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
binTup : Grammar _ CSPTok True (Nat, Nat)
binTup =
  do valA <- natVal
     comma
     valB <- afterMany aSpace natVal
     newline
     pure (valA, valB)

||| A constraint is a declaration, followed by some binary tuples of values.
constraint : Grammar _ CSPTok True Constraint
constraint =
  do decl <- cDecl
     tups <- some binTup
     newline
     pure (MkConstraint decl tups)

||| A Constraint Satisfaction Problem consists of the number of variables to
||| solve, the domains of the variables, and the constraints between them.
csp : Grammar _ CSPTok True CSP
csp =
  do -- FIXME: `count` seems to introduce pain
     -- (S noVars) <- afterMany newline $ nVars
     --    | Z => ?fixme_csp_ambiguous_elab -- pure (MkCSP Z [] []) -- FIXME
     -- doms   <- afterMany newline $ count (exactly (S noVars)) domain
     noVars <- afterMany newline $ nVars
     doms   <- afterMany newline $ some domain
     cs     <- many $ afterMany newline constraint
     -- make sure that noVars matches #domains ; TODO: vects? (see CSP.idr)
     ---   let (Just doms) = toVect noVars (forget someDoms)
     let True = noVars == length doms
          | False => fail "Declared no. vars =/= no. domains in file"
     -- generate the indices (list-comps are inclusive) and index the vars
     ---   let idxs : Vect noVars Nat := map finToNat (range {len=noVars})
     let idxs : List Nat := [0..(noVars `minus` 1)]
     let partVars = map (\i => MkVar i Nothing) idxs
     -- generate the lists of values from the domain bounds
     let listDoms : List (List Nat) := map (\d => [d.lBound..d.uBound]) (toList doms)
     -- finish creating the variables
     let vars = map (\(pv, d) => pv d) $ zip partVars listDoms
     -- convert the constraints to arcs and flatten the result
     let arcs : List Arc := join $ map (\p => [fst p, snd p]) (constrToArcs vars <$> cs)
     pure (MkCSP vars arcs)

||| Parse the given CSP token-stream.
export
parse : List (WithBounds CSPTok) -> Either (List1 (ParsingError CSPTok)) (CSP, List (WithBounds CSPTok))
parse toks = parse csp toks

