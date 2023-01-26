||| A simple forward-checking constraint solver.
module Dai.ForwardChecker

import Dai.CSP
import Dai.Arc
import Dai.Variable

||| Left-branch algorithm for forward-checking.
branchFCLeft :  ?todo_fcLeft

||| Right-branch algorithm for forward-checking.
branchFCRight :  ?todo_fcRight

||| Left-Right branching implementation of the forward-checking constraint
||| solving algorithm.
public export
forwardCheck :  (vars : List Variable)
             -> (soln : List Variable)
             -> List Variable
forwardCheck [] soln = soln  -- assumes all vars in soln are assigned
forwardCheck (var :: vars) soln =
  let soln' = assign (pickVal var) var :: soln
  in ?forwardCheck_rhs_1

