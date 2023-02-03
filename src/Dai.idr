module Dai

import System.File
import Data.List
import Data.SnocList

import public Dai.CSP

-- necessary ?
import public Dai.CSP.Common

---- import public Dai.ForwardChecker
import public Dai.ArcRevisor

public export
solve :  (cspFPath : String)
      -> IO ()
solve cspFPath =
  do (Right cspFHandle) <- openFile cspFPath Read
        | Left fError => putStrLn $ "FileError: \{show fError}"
     (Right csp) <- parseFile cspFHandle
        | Left errMsg => putStrLn $ "----- PARSEFILE ERROR -----\n\{errMsg}"
     ----- putStrLn $ """
     -----            ##### INITIAL PROBLEM #####
     -----            ----- Vars ----
     -----            \{prettyListShow csp.vars}

     -----            ----- Arcs ----
     -----            \{prettyListShow csp.arcs}
     -----            ###########################

     -----            """
     ---- let (True, (soln, _)) = forwardCheck csp.vars csp.arcs [<]
     ----   | (False, (nonSoln, arcs)) =>
     ----         putStrLn $ """
     ----                    No solution found  :'(
     ----                    ##### POST-FC #####
     ----                    ----- Non-solution -----
     ----                    \{prettyListShow nonSoln}
     ----                    ----- Arcs -----
     ----                    \{prettyListShow arcs}
     ----                    ###################
     ----                    """

     let Just (soln, Nothing) = forwardCheck csp.vars csp.arcs csp.vars (Just csp.arcs)
                                -- params: original vars+arcs^ ^solved parts
        | _ => putStrLn "No solution found  :'("
     putStrLn $ "Found a solution!\n\{prettyListShow soln}"

