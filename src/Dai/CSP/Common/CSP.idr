module Dai.CSP.Common.CSP

import Dai.CSP.Common.Arc
import Dai.CSP.Common.Variable

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

