module Dai.ArcRevisor

import Data.List
import Data.Maybe
import Data.SnocList

-- FIXME
import Debug.Trace

import Dai.CSP.Common

%default total

-- FIXME
correct : List Variable -> Bool
correct (a :: (b :: (c :: (d :: [])))) =
  a.assigned == Just 1 && b.assigned == Just 3 && c.assigned == Just 0 && d.assigned == Just 2
correct _ = False

findArc :  (v1 : Variable)
        -> (v2 : Variable)
        -> (arcs : List Arc)
        -> Maybe Arc
findArc v1 v2 arcs =
  case filter (connects v1 v2) arcs of
       [] => Nothing
       (arc :: []) => Just arc
       (arc :: (_ :: _)) => assert_total $ idris_crash "findArc_multiarc_ERROR"

-- does the given value have any support in the given variable's domain, wrt.
-- the given list of valid value pairings?
hasSupport :  (theVal : Nat)
           -> (var : Variable)
           -> (validTups : List (Nat, Nat))
           -> Bool

hasSupport theVal var validTups =
  let tups = map (\domVal => (theVal, domVal)) var.dom
  in any (== True) $ map (\t => elem t validTups) tups

reviseDom :  (fvDom : List Nat)
          -> (currVar : Variable)
          -> (validTups : List (Nat, Nat))
          -> (newDom : SnocList Nat)
          -> List Nat
reviseDom [] currVar validTups newDom = asList newDom
reviseDom (fv :: fvs) currVar validTups newDom =
  if hasSupport fv currVar validTups
     then reviseDom fvs currVar validTups (newDom :< fv)
     else reviseDom fvs currVar validTups newDom

fcRevise :  (fvToVar : Arc)
         -> Maybe Arc
fcRevise fvToVar@(MkArc futVar currVar arcTups) =
  case reviseDom futVar.dom currVar arcTups [<] of
       [] => -- revised domain would be empty, ABORT!!
             Nothing

       revisedDom@(_ :: _) =>
             -- successfully revised domain, update variable and remember to
             -- update variable in the arc as well
             let revisedVar : Variable = { dom := revisedDom } futVar
                 revisedArc : Arc = { from := revisedVar } fvToVar
             in Just revisedArc

-- `oArcs` contain the original arcs given to the function on initial call
--    ^ should NEVER be UPDATED in any way!!
-- `rArcs` contain the continually revised arcs, which are updated as we go
parameters (oVars : List Variable) (oArcs : List Arc)
  fcReviseFutureArcs :  (vars  : List Variable)
                     -> (rArcs : List Arc)
                     -> (currVar : Variable)
                     -> (newVars : SnocList Variable)
                     -> Maybe (List Variable, List Arc)

  fcReviseFutureArcs [] rArcs currVar newVars =
    -- we've exhausted the list of variables without quitting in the process, this
    -- must mean everything went well
    Just (asList newVars, rArcs)

  fcReviseFutureArcs (fv :: fvs) rArcs currVar newVars =
    if fv == currVar
       then -- we don't revise the variable with itself, but we _do_ remember to
            -- keep it!
            fcReviseFutureArcs fvs rArcs currVar (newVars :< fv)
       else -- if there is a relevant arc in the _revised_ arcs, try to revise
            -- it
            case findArc fv currVar rArcs of
                 Nothing => fcReviseFutureArcs fvs rArcs currVar (newVars :< fv)
                 Just arc =>
                  case fcRevise arc of
                       Nothing =>
                          -- arc revision wiped out a domain, ABORT!!
                          trace "\nWIPEOUT\n" $ Nothing

                       (Just revisedArc) =>
                          -- arc revision succeeded, the new arc contains the revised v
                          let fv' = revisedArc.from
                              rArcs' = map (setArcVar fv') rArcs
                          in fcReviseFutureArcs fvs rArcs' currVar (newVars :< fv')

  %default covering

  export
  forwardCheck :  (vars : List Variable)
               -> (arcs : List Arc)
               -> Maybe (List Variable, List Arc)

  branchFCLeft :  (vars : List Variable)
               -> (arcs : List Arc)
               -> (currVar : Variable)
               -> (currVal : Nat)
               -> Maybe (List Variable, List Arc)

  branchFCRight :  (vars : List Variable)
                -> (arcs : List Arc)
                -> (currVar : Variable)
                -> (currVal : Nat)
                -> Maybe (List Variable, List Arc)

  forwardCheck vars arcs =
    if all isJust $ map (.assigned) vars
       then trace "\n\t /!\\ FC has complete assignment: \{show vars}\n" $ Just (vars, arcs)
       else let var = trace "\nFC called with \{show vars}\n\{show arcs}" $ selectVar vars
                val = selectVal var

                -- FIXME: sanity-check; remove once working
                True = length vars == length oVars
                  | False => assert_total $ idris_crash "Gained a variable"

            in case branchFCLeft vars arcs var val of
                    Nothing => branchFCRight vars arcs var val
                    (Just (vars', arcs')) => branchFCRight vars' arcs' var val

  branchFCLeft vars arcs currVar currVal =
    let assignedVar = assign currVar currVal
        -- replace the variable with its assigned version
        vars' = orderedReplace vars assignedVar
        -- and do the same for the arcs (no effect on uninvolved arcs)
        arcs' = map (setArcVar assignedVar) arcs
    in case fcReviseFutureArcs vars' arcs' assignedVar [<] of
            Nothing =>
                -- arc revision wiped out a domain, ABORT!!
                Nothing

            (Just (rVars, rArcs)) =>
                let -- replace the variables with their revised versions
                    vars'' = orderedUpdates vars' rVars
                    -- and likewise for the arcs
                    arcs'' = orderedUpdates arcs' rArcs
                in trace "\n\tBL calls FC with \{show vars''}\n\{prettyListShow arcs''}\n" $ forwardCheck vars'' arcs''

  branchFCRight vars arcs currVar currVal =
    let smallerVar = trace "BR called with \{show vars}\n\{show arcs}\nDeleting \{show currVal} from \{show currVar}\n" $ delVal currVar currVal
    in case smallerVar.dom of
            [] => -- removing the value destroys the domain, ABORT!!
                  Nothing

            (_ :: _) =>
                  let -- replace the variable with its smaller domain version
                      vars' = orderedReplace vars smallerVar
                      -- and do the same for the arcs (no effect on uninvolved arcs)
                      arcs' = map (setArcVar smallerVar) arcs
                  in case fcReviseFutureArcs vars' arcs' smallerVar [<] of
                          Nothing =>
                              -- arc revision wiped out a domain, ABORT!!
                              Nothing
                          (Just (rVars, rArcs)) =>
                              let -- replace the variables with their revised versions
                                  vars'' = orderedUpdates vars' rVars
                                  -- and similar for the arcs
                                  arcs'' = orderedUpdates arcs' rArcs
                              in forwardCheck vars'' arcs''

