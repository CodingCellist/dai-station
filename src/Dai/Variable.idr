module Dai.Variable

||| A variable in a binary CSP, containing:
|||   * its index
|||   * potential assigned value
|||   * its domain (allowed values)
public export
record Variable where
  constructor MkVar

  ||| Variables don't have a name, only an index.
  idx : Nat

  ||| The currently assigned value (if any).
  assigned : Maybe Nat

  ||| The domain (list of permitted assignemnts).
  dom : List Nat

