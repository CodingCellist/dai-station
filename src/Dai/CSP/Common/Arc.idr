module Dai.CSP.Common.Arc

%default total

||| A directed constraint
public export
record Arc where
  constructor MkArc

  from : Nat
  to   : Nat

  validTuples : List (Nat, Nat)

||| Check if an arc is consistent for a given variable assignment.
|||
||| @asmt The assignment to check.
||| @arc  The Arc to check against.
public export
consistent : (asmt : (Nat, Nat)) -> (arc : Arc) -> Bool
consistent asmt arc = consistent' asmt arc.validTuples
  where
    ||| Recurse down the list of valid tuples until a support is found, or the
    ||| list is exhausted.
    consistent' : (asmt : (Nat, Nat)) -> (vtups : List (Nat, Nat)) -> Bool
    consistent' _ [] = False
    consistent' asmt (vtup :: vtups) = asmt == vtup || consistent' asmt vtups
                                       -- case asmt == vtup of
                                       --      False => consistent' asmt vtups
                                       --      True => True

