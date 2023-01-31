module Dai

import System.File
import Data.List
import Data.SnocList

import public Dai.CSP

-- necessary ?
import public Dai.CSP.Common

import public Dai.ForwardChecker

public export
solve :  (cspFPath : String)
      -> IO ()
solve cspFPath =
  do (Right cspFHandle) <- openFile cspFPath Read
        | Left fError => putStrLn $ "FileError: \{show fError}"
     (Right csp) <- parseFile cspFHandle
        | Left errMsg => putStrLn $ "----- PARSEFILE ERROR -----\n\{errMsg}"
     putStrLn $ """
                ##### INITIAL PROBLEM #####
                ----- Vars ----
                \{prettyListShow csp.vars}

                ----- Arcs ----
                \{prettyListShow csp.arcs}
                ###########################

                """
     let (True, (soln, _)) = forwardCheck csp.vars csp.arcs [<]
        | (False, (nonSoln, arcs)) =>
              putStrLn $ """
                         No solution found  :'(
                         ##### POST-FC #####
                         ----- Non-solution -----
                         \{prettyListShow nonSoln}
                         ----- Arcs -----
                         \{prettyListShow arcs}
                         ###################
                         """
     putStrLn $ "Found a solution!\n\{show soln}"
  where
    prettyListShow : Show a => List a -> String
    prettyListShow xs = "[ " ++ foldr (++) "" (intersperse "\n, " (map show xs)) ++ "\n]"

