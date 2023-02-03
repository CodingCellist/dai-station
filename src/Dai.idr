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
      -> IO ()
solve cspFPath =
  do (Right cspFHandle) <- openFile cspFPath Read
        | Left fError => putStrLn $ "FileError: \{show fError}"
     (Right csp) <- parseFile cspFHandle
        | Left errMsg => putStrLn $ "----- PARSEFILE ERROR -----\n\{errMsg}"

     let Just (soln, Nothing) = forwardCheck csp.vars (Just csp.arcs)
        | _ => putStrLn "No solution found  :'("

     putStrLn $ "Found a solution!\n\{prettyListShow soln}"

