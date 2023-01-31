module Dai

import System.File
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
        | Left errMsg => putStrLn $ "---- PARSEFILE ERROR -----\n\{errMsg}"
     let (True, (soln, _)) = forwardCheck csp.vars csp.arcs [<]
        | (False, _) => putStrLn "No solution found  :'("
     putStrLn $ "Found a solution!\n\{show soln}"

