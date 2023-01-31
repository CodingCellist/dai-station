module Dai.CSP.Common.CSP

import Data.Vect

import Dai.CSP.Common.Misc
import Dai.CSP.Common.Arc
import Dai.CSP.Common.Variable

%default total

||| A Constraint Satisfaction Problem (CSP).
public export
record CSP where
  constructor MkCSP

  ||| The variables in the CSP.
  vars : List Variable

  ||| The arcs (i.e. directional constraints) in the CSP.
  arcs : List Arc

--- implementation for if we want to be cool + precise about stuff in the types:
--- data CSP : Type where
---   MkCSP :  {0 noVars : Nat}
---         -> (vars : Vect noVars Variable)
---         -> (arcs : List Arc)
---         -> CSP

------------------------------------------------------------------------
-- Interfaces & Utils

||| By matching on variable indices, replace the variable in the CSP with the
||| given one, preserving variable ordering (CSP is unchanged if no matching
||| variable is found).
||| Additionally, since arcs involve variables, update the relevant arcs to
||| contain the new variable.
public export
updateVar : (csp : CSP) -> (newVar : Variable) -> CSP
updateVar csp@(MkCSP vars arcs) newVar =
  case elem newVar vars of
       False => csp
       True =>
        let vars' = orderedReplace vars newVar
            updArcs = map (setArcVar newVar) arcs
                           -- ^ only affects the arcs which contain newVar
        in { vars := vars', arcs := updArcs } csp

||| By matching on variable indices, replace the arc in the CSP with the given
||| one, preserving arc ordering (CSP is unchanged if no matching arc is found).
public export
updateArc : (csp : CSP) -> (newArc : Arc) -> CSP
updateArc csp@(MkCSP _ arcs) newArc =
  let arcs' = orderedReplace arcs newArc
  in { arcs := arcs' } csp

