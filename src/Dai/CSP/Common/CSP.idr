module Dai.CSP.Common.CSP

import Dai.CSP.Common.Arc
import Dai.CSP.Common.Variable

%default total

||| A Constraint Satisfaction Problem.
public export
record CSP where
  constructor MkCSP

  ||| The number of variables in the CSP
  noVars : Nat

  -- ||| The list of variable domains
  -- doms : List1 CSPPart

  ||| The variables in the CSP
  vars : List Variable

  -- ||| The list of constraints for a variable pair
  -- cs : List CSPPart

  ||| The arcs (directional constraints) in the CSP
  arcs : List Arc

------------------------------------------------------------------------
-- Interfaces & Utils

||| By matching on variable indices, replace the variable in the CSP with the
||| given one, preserving variable ordering (CSP is unchanged if no matching
||| variable is found).
public export
replaceVar : (csp : CSP) -> (newVar : Variable) -> CSP
replaceVar csp@(MkCSP _ vars _) newVar =
  let vars' = orderedReplace vars newVar
  in { vars := vars' } csp
  where
    orderedReplace : List Variable -> Variable -> List Variable
    orderedReplace [] nv = []
    orderedReplace (v :: vs) nv =
      if v == nv
         then nv :: vs
         else v :: (orderedReplace vs nv)

||| By matching on variable indices, replace the arc in the CSP with the given
||| one, preserving arc ordering (CSP is unchanged if no matching arc is found).
public export
replaceArc : (csp : CSP) -> (newArc : Arc) -> CSP
replaceArc csp@(MkCSP _ _ arcs) newArc =
  let arcs' = orderedReplace arcs newArc
  in { arcs := arcs' } csp
  where
    orderedReplace : List Arc -> Arc -> List Arc
    orderedReplace [] na = []
    orderedReplace (a :: as) na =
      if a == na
         then na :: as
         else a :: (orderedReplace as na)

