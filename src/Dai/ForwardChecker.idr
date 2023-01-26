||| A simple forward-checking constraint solver.
module Dai.ForwardChecker

import Dai.CSP.Common

||| Prune future domains for the given variable.
reviseFutureArcs :  (vars : List Variable)
                 -> (arcs : List Arc)
                 -> (var : Variable)
                 -> {default True consistent : Bool}
                 -> ?todo_revFutArc

||| Left-branch algorithm for forward-checking.
branchFCLeft :  (vars : List Variable)
             -> (arcs : List Arc)
             -> (var : Variable)
             -> (val : Nat)
             -> ?todo_fcLeft

||| Right-branch algorithm for forward-checking.
branchFCRight :  ?todo_fcRight

||| Left-Right branching implementation of the forward-checking constraint
||| solving algorithm.
public export
forwardCheck :  (vars : List Variable)
             -> (arcs : List Arc)
             -> (soln : List Variable)
             -> List Variable
forwardCheck [] arcs soln = soln  -- assumes all vars in soln are assigned
forwardCheck (var :: vars) arcs soln =
  let val = pickVal var
  in ?forwardCheck_rhs_1

