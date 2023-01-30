||| Miscellaneous utils which probably should be better organised/added to the
||| stdlib, but go in here for now.
module Dai.CSP.Common.Misc

%default total

||| Replace an element in the given list while preserving the ordering of
||| elements. Assumes the list contains unique elements in a significant order.
public export
orderedReplace : Eq a => List a -> a -> List a
orderedReplace [] y = []
orderedReplace (x :: xs) y =
  if x == y
     then y :: xs
     else x :: orderedReplace xs y

||| Update the given originals using the given list of updated versions.
|||
||| Traverses the `upds` list, calling `orderedReplace` on each element while
||| making sure to thread the new list of elements (which may contain updated
||| _and_ original arcs).
public export
orderedUpdates : Eq a => (origs : List a) -> (upds : List a) -> List a
orderedUpdates origs [] = origs
orderedUpdates origs (upd :: upds) =
  let oneUpdate = orderedReplace origs upd
  in orderedUpdates oneUpdate upds

