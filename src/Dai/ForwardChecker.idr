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

||| Prune the domains of the future variables according to their connecting
||| arcs. Helper function for `reviseFutureArcs`.
|||
||| @return Whether the domains are still non-empty, along with the updated
|||         future vars and arcs.
reviseFutureVars :  (fvs : List Variable)
                 -> (arcs : List Arc)
                 -> {default True consistent : Bool}
                 -> (var : Variable)
                 -> (prunedFVs : SnocList Variable)
                 -> (Bool, (List Variable, List Arc))

reviseFutureVars [] arcs var prunedFVs =
  (consistent, (asList prunedFVs, arcs))

reviseFutureVars oFVs@(fv :: fvs) oArcs var prunedFVs =
  let [arc] = filter (connects fv var) oArcs
        | [] => reviseFutureVars fvs oArcs var (prunedFVs :< fv)
                -- ^ no arc found => nothing to revise, so just keep going?
                --   I think this is fine?...
        | _  => ?reviseFV_multiarc_ERROR

      (True, arc') = reviseArc arc
        | (False, _) => (False, (oFVs, oArcs))

      -- caution: arc' contains a pruned Variable, which needs to be
      --          synchronised/distributed to all relevant places
      prunedFVs' = prunedFVs :< arc'.from
      arcs' = orderedReplace oArcs arc'

      -- now, recall that this was only for `fv`; still need `fvs`
      (True, prunedFVsArcs) = reviseFutureVars fvs arcs' var prunedFVs'
        | (False, _) => (False, (oFVs, oArcs))

  in (True, prunedFVsArcs)

||| Prune future domains for the given variable, **propagating the updated arcs
||| and variables (containing domains)** to the new CSP which is returned.
|||
||| @return whether all domains remain intact, and the potentially updated CSP
reviseFutureArcs :  (csp : CSP)
                 -> (var : Variable)
                 -> {default True consistent : Bool}
                 -> (Bool, CSP)   -- `consistent`, and updated CSP
reviseFutureArcs csp var =
  let futVars = filter (/= var) csp.vars
  in case futVars of
          [] => (consistent, csp)
          (fv :: fvs) =>
            let -- prune future variable domains via arc revision
                (True, (fvs', arcs')) = reviseFutureVars (fv :: fvs) csp.arcs var [<]
                  | (False, _) => (False, csp)  -- domain wipeout, restore orig.

                -- now we have a big collection of updated stuff...
                -- we need to be **extremely careful** to propagate these
                -- updated things to where they're needed!

                newCSPArcs = updateArcs csp.arcs arcs'
                newCSPVars = updateVars csp.vars fvs'
                -- note that since the list of future variables is created by
                -- filtering out `var`, running the update operation above
                -- should not change `var` itself, which is what we want!

                -- apply the updates
                csp' : CSP := { arcs := newCSPArcs, vars := newCSPVars } csp

            in (True, csp')   -- if we somehow got here, it's all good!

            where
              ||| Update all the original arcs using the list of updated arcs.
              |||
              ||| Traverses the `upds` list, calling `orderedReplace` on each
              ||| one while making sure to thread the list of new arcs (which
              ||| may contain updated _and_ original arcs).
              %inline
              updateArcs : (oArcs : List Arc) -> (upds : List Arc) -> List Arc
              updateArcs oArcs upds = orderedUpdates oArcs upds

              ||| Update all the original arcs using the list of updated arcs.
              |||
              ||| Traverses the `upds` list, calling `orderedReplace` on each
              ||| one while making sure to thread the list of new arcs (which
              ||| may contain updated _and_ original arcs).
              %inline
              updateVars : (oVars : List Variable) -> (upds : List Variable) -> List Variable
              updateVars oVars upds = orderedUpdates oVars upds


||| Left-branch algorithm for forward-checking.
|||
||| Returns whether branching+revision was successful, along with the
||| potentially updated `CSP`.
branchFCLeft :  (csp : CSP)
             -> (var : Variable)
             -> (val : Nat)
             -> (Bool, CSP)


||| Right-branch algorithm for forward-checking.
branchFCRight :  ?todo_fcRight


||| Left-Right branching implementation of the forward-checking constraint
||| solving algorithm.
public export
forwardCheck :  (csp : CSP)
             -> (soln : List Variable)
             -> ?todo_fc


branchFCLeft csp var val =
  let assignedVar = assign var val
  in case reviseFutureArcs csp assignedVar of
          (False, _) => (False, csp)  -- things went wrong, keep csp intact
          (True, revisedCSP) =>
            let -- arc-consistency holds post-revision, so keep going
                csp' = updateVar revisedCSP assignedVar
                -- TODO: figure out `varList - var` in fc recursion
            in (True, ?hole)


--- forwardCheck [] arcs soln = soln  -- assumes all vars in soln are assigned
--- forwardCheck (var :: vars) arcs soln =
---   let val = pickVal var
---   in ?forwardCheck_rhs_1

