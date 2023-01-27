||| A simple forward-checking constraint solver.
module Dai.ForwardChecker

import Dai.CSP.Common

%default total

||| Prune the domain of the `from` variable according to the arc's valid tuples.
reviseArc : Arc -> Arc
reviseArc arc = ?reviseArc_rhs
  where
    ||| Check if the given assignment has at least one matching valid tuple when
    ||| combined with the domain of v2, i.e. its possible pairings, and prune
    ||| the assigned value from the variable's domain if it doesn't.
    |||
    ||| @return Whether the domain is non-empty, and the updated variable
    prune : (Variable, Nat) -> (v2 : Variable) -> (Bool, Variable)
    prune (v1, v1Assign) v2 =
      let hasSupport = any (\v2Val => elem (v1Assign, v2Val) arc.validTuples) v2.dom
          -- TODO: some cleverness with whether or not to prune the domain
      in ?revise_rhs_0
         -- TODO: followed by the actual assignment and empty check

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

