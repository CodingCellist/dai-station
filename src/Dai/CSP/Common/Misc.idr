{-
 - A constraint solver written in Idris2
 - Copyright (c) 2023, Thomas E. Hansen (CodingCellist)
 - SPDX-License-Identifier: BSD-3-Clause
 -}

||| Miscellaneous utils which probably should be better organised/added to the
||| stdlib, but go in here for now.
module Dai.CSP.Common.Misc

import Data.List

%default total

||| Replace an element in the given list while preserving the ordering of
||| elements. Assumes the list contains unique elements in a significant order.
public export
orderedReplace : Eq a => List a -> a -> List a
orderedReplace [] new = []
orderedReplace (old :: xs) new =
  if old == new
     then new :: xs
     else old :: orderedReplace xs new

||| Update the given originals using the given list of updated versions.
|||
||| Traverses the `upds` list, calling `orderedReplace` on each element while
||| making sure to thread the new list of elements (which may contain updated
||| _and_ original elements).
public export
orderedUpdates : Eq a => (todo : List a) -> (upds : List a) -> List a
orderedUpdates done [] = done
orderedUpdates todo (upd :: upds) =
  let oneUpdate = orderedReplace todo upd
  in orderedUpdates oneUpdate upds

export
prettyListShow : Show a => List a -> String
prettyListShow xs = "[ " ++ foldr (++) "" (intersperse "\n, " (map show xs)) ++ "\n]"

