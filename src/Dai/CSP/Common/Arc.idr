module Dai.CSP.Common.Arc

import Dai.CSP.Common.Variable

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

||| Prune the domains
revise : Arc -> Arc

------------------------------------------------------------------------
-- Interfaces & Utils

||| Returns True iff the Arc goes from the first given variable to the second.
public export
connects : (v1 : Variable) -> (v2 : Variable) -> (a : Arc) -> Bool
connects v1 v2 a = a.from == v1.idx  &&  a.to == v2.idx

public export
Eq Arc where
  (==) (MkArc from1 to1 tups1) (MkArc from2 to2 tups2) =
    from1 == from2  &&  to1 == to2  &&  tups1 == tups2
  -- checking tups for sanity: sometimes we rm stuff from those lists

