module Dai.ArcRevisor

import Data.List
import Data.Maybe
import Data.SnocList

import Dai.CSP.Common

-- omit the footgun; use `getDom` instead
%hide (.dom)

%default total

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
  let pairings : List (Nat, Nat) = map (MkPair theVal) (getDom var)
  in anyValid pairings validTups
  where
    isValid : (pairing : (Nat, Nat)) -> List (Nat, Nat) -> Lazy Bool
    isValid pairing [] = False
    isValid pairing (valid :: valids) =
      ---- pairing == valid || isValid pairing valids
      case pairing == valid of
           True => True
           False => isValid pairing valids

    anyValid : (pairings : List (Nat, Nat)) -> List (Nat, Nat) -> Lazy Bool
    anyValid _ [] = False   -- no more valids to test against, so no
    anyValid [] (valid :: valids) = False   -- no, none of them were valid
    anyValid (pair :: pairs) (valid :: valids) =
      -- if the first pairing is fine, we're done; if not, try the next one
      isValid pair (valid :: valids) || anyValid pairs (valid :: valids)

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
             let revisedVar : Variable = { dom := revisedDom } futVar
                 revisedArc : Arc = { from := revisedVar } fvToVar
             in Just revisedArc


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
                        Nothing

                     (Just revisedArc) =>
                        -- arc revision succeeded, the new arc contains the revised v
                        let fv' = revisedArc.from
                            rArcs' = map (setArcVar fv') rArcs
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

------------------------------------------------------------------------
-- Forward-Check

-- if we've lost the arcs, we must be done (we can't revise anything)
forwardCheck vars Nothing = Just (vars, Nothing)

-- check if we're done, and if so remove the arcs; otherwise keep going
forwardCheck vars (Just arcs) =
  if all isJust $ map (.assigned) vars
     then Just (vars, Nothing)
     else let var = selectVar vars
              val = selectVal var
          in case branchFCLeft vars (Just arcs) var val of
                  Nothing => branchFCRight vars (Just arcs) var val
                  (Just (vars', Nothing)) => branchFCRight vars' Nothing var val
                  (Just (vars', Just (arcs'))) => branchFCRight vars' (Just arcs') var val

------------------------------------------------------------------------
-- Branch Left

-- if we've lost the arcs, we must be done (we can't revise anything)
branchFCLeft vars Nothing currVar currVal = Just (vars, Nothing)

-- otherwise, proceed with assignment and arc revision
branchFCLeft vars (Just arcs) currVar currVal =
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
              in forwardCheck vars'' (Just arcs'')


------------------------------------------------------------------------
-- Branch Right

-- if we've lost the arcs, we must be done (we can't revise anything)
branchFCRight vars Nothing currVar currVal = Just (vars, Nothing)

-- otherwise, proceed with removing the bad value and revising the arcs
branchFCRight vars (Just arcs) currVar currVal =
  let smallerVar = delVal currVar currVal
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

