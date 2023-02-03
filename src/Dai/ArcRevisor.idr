module Dai.ArcRevisor

import Data.List
import Data.Maybe
import Data.SnocList

-- FIXME
import Debug.Trace

import Dai.CSP.Common

-- omit the footgun; use `getDom` instead
%hide (.dom)

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
       (arc :: []) => trace "\tFound arc \{show arc}" $ Just arc
       (arc :: (_ :: _)) => assert_total $ idris_crash "findArc_multiarc_ERROR"

-- does the given value have any support in the given variable's domain, wrt.
-- the given list of valid value pairings?
hasSupport :  (theVal : Nat)
           -> (var : Variable)
           -> (validTups : List (Nat, Nat))
           -> Bool
hasSupport theVal var validTups =
  let pairings : List (Nat, Nat) = map (MkPair theVal) (getDom var)
  in anyValid pairings validTups
  where
    isValid : (pairing : (Nat, Nat)) -> List (Nat, Nat) -> Lazy Bool
    isValid pairing [] = trace "\tNo support found for \{show pairing}" $ False
    isValid pairing (valid :: valids) =
      ---- pairing == valid || isValid pairing valids
      case pairing == valid of
           True => trace "\tPairing \{show pairing} supported by \{show valid}" True
           False => isValid pairing valids

    anyValid : (pairings : List (Nat, Nat)) -> List (Nat, Nat) -> Lazy Bool
    anyValid _ [] = False   -- no more valids to test against, so no
    anyValid [] (valid :: valids) = False   -- no, none of them were valid
    anyValid (pair :: pairs) (valid :: valids) =
      -- if the first pairing is fine, we're done; if not, try the next one
      isValid pair (valid :: valids) || anyValid pairs (valid :: valids)

----    anySupport cand [] = False
----    anySupport cand (valid :: valids) = cand == valid || anySupport cand valids

--- hasSupport theVal var validTups =
---   let tups = map (\domVal => (theVal, domVal)) var.dom
---   in any (== True) $ map (\t => elem t validTups) tups

reviseDom :  (fvDom : List Nat)
          -> (currVar : Variable)
          -> (validTups : List (Nat, Nat))
          -> (newDom : SnocList Nat)
          -> List Nat
reviseDom [] currVar validTups newDom = toList newDom
reviseDom (fv :: fvs) currVar validTups newDom =
  if hasSupport fv currVar validTups
     then reviseDom fvs currVar validTups (newDom :< fv)
     else reviseDom fvs currVar validTups newDom

fcRevise :  (fvToVar : Arc)
         -> Maybe Arc
fcRevise fvToVar@(MkArc futVar currVar arcTups) =
  case reviseDom (getDom futVar) currVar arcTups [<] of
       [] => -- revised domain would be empty, ABORT!!
             Nothing

       revisedDom@(_ :: _) =>
             -- successfully revised domain, update variable and remember to
             -- update variable in the arc as well
             let revisedVar : Variable = trace "\tRevised domain is \{show revisedDom}" $ { dom := revisedDom } futVar
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
                          trace "\tWiped out domain of \{show fv}, ABORT\n" $ Nothing

                       (Just revisedArc) =>
                          -- arc revision succeeded, the new arc contains the revised v
                          let fv' = revisedArc.from
                              rArcs' = trace "\tSuccessfully revised \{show fv} to \{show fv'}" $ map (setArcVar fv') rArcs
                          in fcReviseFutureArcs fvs rArcs' currVar (newVars :< fv')

  %default covering

  export
  forwardCheck :  (vars : List Variable)
               -> (arcs : Maybe (List Arc))
               -> Maybe (List Variable, Maybe (List Arc))

  branchFCLeft :  (vars : List Variable)
               -> (arcs : Maybe (List Arc))
               -> (currVar : Variable)
               -> (currVal : Nat)
               -> Maybe (List Variable, Maybe (List Arc))

  branchFCRight :  (vars : List Variable)
                -> (arcs : Maybe (List Arc))
                -> (currVar : Variable)
                -> (currVal : Nat)
                -> Maybe (List Variable, Maybe (List Arc))


  forwardCheck vars Nothing = Just (vars, Nothing)
  forwardCheck vars (Just arcs) =
    if all isJust $ map (.assigned) vars
       --- then trace "\n\t /!\\ FC has complete assignment: \{show vars}\n\n" $ Just (vars, arcs)
       ---- then assert_total $ idris_crash "FOUND SOLUTION:\n\{prettyListShow vars}\n"
       then Just (vars, Nothing)
       else let var = trace "\n¤ FC called with \{show vars}\n\{prettyListShow arcs}\n\n" $ selectVar vars
                val = trace "FC selects var \{show var}" $ selectVal var

                -- FIXME: sanity-check; remove once working
                True = trace "FC selects \{show var} := \{show val}\n" $ length vars == length oVars
                  | False => assert_total $ idris_crash "Gained a variable"

            in case branchFCLeft vars (Just arcs) var val of
                    Nothing => branchFCRight vars (Just arcs) var val
                    (Just (vars', Nothing)) => branchFCRight vars' Nothing var val
                    (Just (vars', Just (arcs'))) => branchFCRight vars' (Just arcs') var val


  branchFCLeft vars Nothing currVar currVal = Just (vars, Nothing)
  branchFCLeft vars (Just arcs) currVar currVal =
    let assignedVar = trace "BL called with \{show vars}\t\{show currVar}:=\{show currVal}\n" $ assign currVar currVal
        -- replace the variable with its assigned version
        vars' = trace "BL assigns \{show currVar} := \{show currVal}\n" $ orderedReplace vars assignedVar
        -- and do the same for the arcs (no effect on uninvolved arcs)
        arcs' = trace "BL calls revise on \{show vars'}" $ map (setArcVar assignedVar) arcs
    in case fcReviseFutureArcs vars' arcs' assignedVar [<] of
            Nothing =>
                -- arc revision wiped out a domain, ABORT!!
                Nothing

            (Just (rVars, rArcs)) =>
                let -- replace the variables with their revised versions
                    vars'' = orderedUpdates vars' rVars
                    -- and likewise for the arcs
                    arcs'' = orderedUpdates arcs' rArcs
                in trace "\n\tBL calls FC with \{show vars''}\n\{prettyListShow arcs''}\n" $ forwardCheck vars'' (Just arcs'')


  branchFCRight vars Nothing currVar currVal = Just (vars, Nothing)
  branchFCRight vars (Just arcs) currVar currVal =
    let smallerVar = trace "BR called with \{show vars}\nBR deletes \{show currVal} from \{show currVar}\n" $ delVal currVar currVal
    in case (getDom smallerVar) of
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
                              in forwardCheck vars'' (Just arcs'')

