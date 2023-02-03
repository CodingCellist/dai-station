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

     let Just (soln, Nothing) = forwardCheck csp.vars (Just csp.arcs)
        | _ => putStrLn "No solution found  :'("

     putStrLn $ "Found a solution!\n\{prettyListShow soln}"

