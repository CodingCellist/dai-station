{-
 - A constraint solver written in Idris2
 - Copyright (c) 2023, Thomas E. Hansen (CodingCellist)
 - SPDX-License-Identifier: BSD-3-Clause
 -}

module Dai.CSP.Common.Arc

import Dai.CSP.Common.Variable

%default total

||| A directed constraint
public export
record Arc where
  constructor MkArc

  from : Variable
  to   : Variable

  validTuples : List (Nat, Nat)


------------------------------------------------------------------------
-- Interfaces & Utils

||| Set the corresponding variable in the Arc to the new one, returning the
||| resulting arc. If neiter the `to` or the `from` variable match, the given
||| Arc is returned unchanged.
public export
setArcVar : (newVar : Variable) -> (oArc : Arc) -> Arc
setArcVar newVar oArc =
  case oArc.from == newVar of
       True => { from := newVar } oArc
       False =>
          case oArc.to == newVar of
               True => { to := newVar } oArc
               False => oArc

||| Returns True iff the Arc goes from the first given variable to the second.
public export
connects : (v1 : Variable) -> (v2 : Variable) -> (a : Arc) -> Bool
connects v1 v2 a = a.from == v1  &&  a.to == v2

public export
Eq Arc where
  (==) (MkArc from1 to1 tups1) (MkArc from2 to2 tups2) =
    from1 == from2  &&  to1 == to2

public export
Show Arc where
  show (MkArc from to validTuples) =
    "<v\{show from.idx} --> v\{show to.idx} :\t\{show validTuples}>"

