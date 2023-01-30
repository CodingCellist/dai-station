||| Miscellaneous utils which probably should be better organised/added to the
||| stdlib, but go in here for now.
module Dai.CSP.Common.Misc

||| Replace an element in the given list while preserving the ordering of
||| elements. Assumes the list contains unique elements in a significant order.
public export
orderedReplace : Eq a => List a -> a -> List a
orderedReplace [] y = []
orderedReplace (x :: xs) y =
  if x == y
     then y :: xs
     else x :: orderedReplace xs y

