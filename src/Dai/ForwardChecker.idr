{-
 - A constraint solver written in Idris2
 - Copyright (c) 2023, Thomas E. Hansen (CodingCellist)
 - SPDX-License-Identifier: BSD-3-Clause
 -}

module Dai.ForwardChecker

import Data.List
import Data.Maybe
import Data.SnocList

import Dai.CSP.Common


-- omit the footgun; use `getDom` instead
%hide (.dom)


%default total


||| Retrieve the arc going from v1 to v2, if one exists.
||| It is an error for there to be more than one arc between the variables.
findArc :  (v1 : Variable)
        -> (v2 : Variable)
        -> (arcs : List Arc)
        -> Maybe Arc
findArc v1 v2 arcs =
  case filter (connects v1 v2) arcs of
       [] => Nothing
       (arc :: []) => Just arc
       (arc :: (_ :: _)) => assert_total $ idris_crash "findArc_multiarc_ERROR"


||| Check if the given value has a support in the given variable's domain, i.e.
||| check if any pairing with the domain is in the list of accepted tuples.
hasSupport :  (theVal : Nat)
           -> (var : Variable)
           -> (validTups : List (Nat, Nat))
           -> Bool
hasSupport theVal var validTups =
  let pairings = map (MkPair theVal) (getDom var)
  in any (\pairing => elem pairing validTups) pairings


||| Traverse `fvDom`, keeping only the values which are supported by `currVar`'s
||| domain wrt. the list of accepted tuples. The resulting list is the new
||| domain for `fvDom`.
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

||| Revise the `from` variable of the given arc, i.e. compute its new domain and
||| assign it. If a domain wipeout occurs, something's gone wrong with the
||| current attempt, and so no new state is returned.
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


||| Revise the arcs between the variables other than `currVar` (which we are
||| revising against).
|||
||| This prunes the domains of the other variables wrt. the current domain or
||| value assignment. Returns the list of updated variables if no domains were
||| wiped out, and `Nothing` otherwise (i.e. discards any partial state-update).
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


-- with all the state updates going on, we have to default to `covering` here.
%default covering


------------------------------------------------------------------------
-- Forward-checking's function declarations


||| Solve the given constraint problem using 2-way branching forward-checking.
|||
||| @vars The list of variables to solve.
||| @arcs The list of arcs (directional constraints) constraining the variables.
|||       The recursive calls set this to `Nothing` when a solution is found.
|||
||| @return The assigned variables along with no arcs, if a solution was found;
|||         the original state of the problem otherwise.
public export
forwardCheck :  (vars : List Variable)
             -> (arcs : Maybe (List Arc))
             -> Maybe (List Variable, Maybe (List Arc))


||| Attempt to assign the given variable to the given value, then revise the
||| arcs to see if this assignment maintains arc-consistency.
|||
||| @return The new state if arc revision was successful, and `Nothing`
|||         otherwise. The new arcs become `Nothing` when a solution is found.
branchFCLeft :  (vars : List Variable)
             -> (arcs : Maybe (List Arc))
             -> (currVar : Variable)
             -> (currVal : Nat)
             -> Maybe (List Variable, Maybe (List Arc))

||| Remove the bad value from the given variable's domain, check that we haven't
||| wiped out the domain by doing so, and if not, then revise the arcs to check
||| that arc-consistency is maintained despite the smaller domain.
|||
||| @return The new state if the domain was not wiped out and arc revision was
|||         successful, and `Nothing` otherwise. The new arcs become `Nothing`
|||         when a solution is found.
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

