||| A simple forward-checking constraint solver.
module Dai.ForwardChecker

import Dai.CSP.Common

||| Prune future domains for the given variable.
reviseFutureArcs :  (csp : CSP)
                 -> (var : Variable)
                 -> {default True consistent : Bool}
                 -> (Bool, CSP)   -- `consistent`, and updated CSP
reviseFutureArcs csp var =
  let futVars = filter (/= var) csp.vars
  in case futVars of
          [] => (consistent, csp)
          (fv :: fvs) =>
            let [arc] = filter (connects fv var) csp.arcs
                  | [] => ?reviesFA_no_arcs_ERROR
                  | _ => ?reviesFA_multiarc_ERROR
            in ?reviseFutureArcs_rhs_1

||| Left-branch algorithm for forward-checking.
branchFCLeft :  (csp : CSP)
             -> (var : Variable)
             -> (val : Nat)
             -> ?todo_fcLeft

||| Right-branch algorithm for forward-checking.
branchFCRight :  ?todo_fcRight

||| Left-Right branching implementation of the forward-checking constraint
||| solving algorithm.
public export
forwardCheck :  (csp : CSP)
             -> (soln : List Variable)
             -> ?todo_fc

--- forwardCheck [] arcs soln = soln  -- assumes all vars in soln are assigned
--- forwardCheck (var :: vars) arcs soln =
---   let val = pickVal var
---   in ?forwardCheck_rhs_1

