{-
 - A constraint solver written in Idris2
 - Copyright (c) 2023, Thomas E. Hansen (CodingCellist)
 - SPDX-License-Identifier: BSD-3-Clause
 -}

module Dai

import System.File
import Data.List
import Data.SnocList

import public Dai.CSP

import public Dai.ForwardChecker

public export
solve :  (cspFPath : String)
      -> (heu : Maybe Heuristic)
      -> IO ()
solve cspFPath heu =
  do (Right cspFHandle) <- openFile cspFPath Read
        | Left fError => putStrLn $ "FileError: \{show fError}"
     (Right csp) <- parseFile cspFHandle
        | Left errMsg => putStrLn $ "----- PARSEFILE ERROR -----\n\{errMsg}"

     -- Before we even try to solve, ensure the problem is arc-consistent in the
     -- first place (i.e. ensure the domains only contain consistent values).
     -- If this fails, the problem was inconsistent from the get-go.
     let Just (vars, arcs) = initArcConsist csp.vars csp.arcs csp.vars
        | Nothing => putStrLn "No solution possible: CSP is not arc-consistent."


     let Just (soln, Nothing) = forwardCheck vars (Just arcs) heu
        | _ => putStrLn "No solution found  :'("

     putStrLn $ "Found a solution!\n\{prettyListShow soln}"
  where
    ||| Traverse the list of variables, enforcing arc consistency against each
    ||| variable and "accumulating" the result.
    initArcConsist :  List Variable
                   -> List Arc
                   -> List Variable
                   -> Maybe (List Variable, List Arc)
    initArcConsist [] arcs newVars = Just (newVars, arcs)
    initArcConsist (iVar :: iVars) arcs newVars =
      case fcReviseFutureArcs (iVar :: iVars) arcs iVar [<] of
           Nothing => Nothing   -- inconsistent; ABORT!!
           (Just (revdVars, revdArcs)) =>
              -- recall that arc revision doesn't affect current variable
              let iVars' = orderedUpdates iVars revdVars
                  arcs' = orderedUpdates arcs revdArcs
                  newVars' = orderedUpdates newVars revdVars
              in initArcConsist iVars' arcs' newVars'

