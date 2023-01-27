||| A simple forward-checking constraint solver.
module Dai.ForwardChecker

import Data.SnocList

import Dai.CSP.Common

%default total

||| Prune the domain of the `from` Variable according to the arc's valid tuples,
||| returning whether the domain remains non-empty after the pruning along with
||| the updated arc.
reviseArc : Arc -> (Bool, Arc)
reviseArc arc@(MkArc arcFrom arcTo validTuples) =
  case newDom arcFrom.dom [<] of
       [<]  => (False, arc)
       dom' => let prunedFrom : Variable := { dom := asList dom' } arcFrom
                   arc' = { from := prunedFrom } arc
               in (True, arc')
  where
    ||| Check if the given assignment value has at least one matching valid
    ||| tuple when combined with the domain of the arc's `to` Variable, i.e. its
    ||| possible pairings.
    supported : Nat -> Bool
    supported hypAssign =
      any (\v2Val => elem (hypAssign, v2Val) validTuples) arcTo.dom


    ||| Compute the new domain of the given variable, based on the current arc.
    newDom : List Nat -> (acc : SnocList Nat) -> SnocList Nat
    newDom [] acc = acc
    newDom (dv :: dvs) acc =
      if supported dv
         then newDom dvs (acc :< dv)
         else newDom dvs acc

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
                  | [] => ?reviseFA_no_arcs_ERROR
                  | _  => ?reviseFA_multiarc_ERROR

                (True, arc') = reviseArc arc
                  | (False, _) => (False, csp)  -- domain wipeout, don't update

                -- caution: arc' contains a pruned Variable, which needs to be
                --          synchronised/distributed to all relevant places
                partCSP' = replaceVar csp (arc'.from)
                fvCSP' = replaceArc partCSP' arc'

                -- now, recall that this was only for `fv`; still need `fvs`
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

